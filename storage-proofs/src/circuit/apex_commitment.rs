use bellman::{ConstraintSystem, SynthesisError};
use pairing::Engine;
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num;
use sapling_crypto::circuit::num::AllocatedNum;

use crate::circuit::constraint::equal;

#[derive(Clone)]
pub enum ApexCommitment<E: Engine> {
    Leaf(AllocatedNum<E>),
    Branch(Box<ApexCommitment<E>>, Box<ApexCommitment<E>>),
}

impl<E: Engine> ApexCommitment<E> {
    #[allow(dead_code)]
    fn new(allocated_nums: &[AllocatedNum<E>]) -> ApexCommitment<E> {
        let commitments = allocated_nums;

        let size = allocated_nums.len();
        assert!(size > 0, "BinaryCommitment must not be empty.");

        if size == 1 {
            return ApexCommitment::Leaf(commitments[0].clone());
        }

        assert_eq!(
            size.count_ones(),
            1,
            "BinaryCommitment size must be a power of two."
        );

        let half_size = size / 2;
        let left = Self::new(&commitments[0..half_size]);
        let right = Self::new(&commitments[half_size..]);

        ApexCommitment::Branch(Box::new(left), Box::new(right))
    }

    fn at_path<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        path: &[Boolean],
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        let length = path.len();

        match self {
            ApexCommitment::Leaf(allocated_num) => {
                assert_eq!(length, 0, "Path too long for BinaryCommitment size.");

                Ok((*allocated_num).clone())
            }
            ApexCommitment::Branch(left_boxed, right_boxed) => {
                assert!(length > 0, "Path too short for BinaryCommitment size.");
                let curr_is_right = &path[0];
                let cs = &mut cs.namespace(|| {
                    format!(
                        "path-{}",
                        if curr_is_right.get_value().unwrap() {
                            "1"
                        } else {
                            "0"
                        }
                    )
                });

                let (left, right) = match ((**left_boxed).clone(), (**right_boxed).clone()) {
                    (ApexCommitment::Leaf(left), ApexCommitment::Leaf(right)) => (left, right),
                    (left_comm, right_comm) => {
                        let next_path = &path[1..];
                        let left = left_comm.at_path(&mut cs.namespace(|| "left"), next_path)?;
                        let right = right_comm.at_path(&mut cs.namespace(|| "right"), next_path)?;
                        (left, right)
                    }
                };

                let (xl, _xr) = num::AllocatedNum::conditionally_reverse(
                    cs.namespace(|| "conditional reversal of BinaryCommitment elements"),
                    &left,
                    &right,
                    &curr_is_right,
                )?;

                Ok(xl)
            }
        }
    }

    pub fn includes<A, AR, CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        annotation: A,
        num: &num::AllocatedNum<E>,
        path: &[Boolean],
    ) -> Result<(), SynthesisError>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let cs = &mut cs.namespace(|| "binary_commitment_inclusion");
        let num_at_path = self.at_path(cs, path)?;

        Ok(equal(cs, annotation, num, &num_at_path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::test::TestConstraintSystem;
    use bellman::ConstraintSystem;
    use pairing::bls12_381::Bls12;
    use pairing::Engine;
    use rand::{Rng, SeedableRng, XorShiftRng};
    use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
    use sapling_crypto::circuit::num::AllocatedNum;

    fn path_from_index<E: Engine, CS: ConstraintSystem<E>>(
        cs: &mut CS,
        index: usize,
        size: usize,
    ) -> Vec<Boolean> {
        let mut path = Vec::new();
        for i in 0..size {
            let boolean = <Boolean as std::convert::From<AllocatedBit>>::from(
                AllocatedBit::alloc(cs.namespace(|| format!("position bit {}", i)), {
                    let bit = ((index >> i) & 1) == 1;
                    Some(bit)
                })
                .unwrap(),
            );

            path.push(boolean);
        }
        // TODO: Can we avoid this reversal?
        path.reverse();

        path
    }

    // How many constraints?
    //
    // Experimentally, we know:
    // size 1,   n = 0 -> 1
    // size 2,   n = 1 -> 8
    // size 4,   n = 2 -> 36
    // size 8,   n = 3 -> 144
    // size 16,  n = 4 -> 560
    // size 32,  n = 5 -> 2176
    // size 64,  n = 6 -> 8152
    // size 128, n = 7 -> 3356
    //
    // Algorithm:
    //   size 2^n, n = n
    //   constraints(n) -> (2^n * n) + ((2^n+1 - 1) * 2^n)
    //
    // Example calculations:
    // n = 0; 1 + 0                = 1
    // n = 1; 2 + (4-1)*2          = 8
    // n = 2; 4 * 2 + (8-1)*4      = 36
    // n = 3; 8 * 3 + (16-1)*8     = 144
    // n = 4; 16 * 4 + (32-1) * 16 = 560
    // n = 8; 32 * 5 + (64-1) * 32 = 2176
    //
    // TODO: The actual complexity of per-test constraint-generation should be O(2^n).
    // Conceptually, we need to convert the constraint-generation from un-memoized recursion
    // to dynamic programming. However, we don't have real conditionals. Working only with the
    // swap-if primitive (which we do have), we can't do that in the obvious way.
    //
    // However, there is a really pretty way to achieve the same result by repeatedly transforming
    // the apex leaves as we walk toward the root.
    //
    // Implement that.
    fn constraints(n: usize) -> usize {
        let two_to_the_n = 1 << n;
        let two_to_the_n_plus_one = 2 * two_to_the_n;

        (two_to_the_n * n) + (two_to_the_n_plus_one - 1) * two_to_the_n
    }

    #[test]
    fn binary_commitment_circuit() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let max_len = 8;

        for n in 0..max_len {
            let size = 1 << n;
            let mut cs = TestConstraintSystem::<Bls12>::new();
            let mut nums = Vec::with_capacity(size);
            for i in 0..size {
                let val: <Bls12 as Engine>::Fr = rng.gen();
                let cs = &mut cs.namespace(|| format!("num-{}", i));
                let num = AllocatedNum::alloc(cs, || Ok(val)).unwrap();

                nums.push(num);
            }

            let bc = ApexCommitment::new(&nums);

            for (i, num) in nums.iter().enumerate() {
                let cs = &mut cs.namespace(|| format!("test index {}", i));
                let path = path_from_index(cs, i, n);

                bc.includes(cs, || format!("inclusion check {}", i), num, &path)
                    .unwrap();
            }

            assert_eq!(cs.num_constraints(), constraints(n));
            assert!(cs.is_satisfied(), "constraints not satisfied");
        }
    }
}
