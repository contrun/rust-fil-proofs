use bellman::{ConstraintSystem, SynthesisError};
use pairing::Engine;
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::num;
use sapling_crypto::circuit::num::AllocatedNum;

use crate::circuit::constraint::equal;

pub trait ApexCommitment<E: Engine> {
    fn new(allocated_nums: &[AllocatedNum<E>]) -> Self;

    fn includes<A, AR, CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        annotation: A,
        num: &num::AllocatedNum<E>,
        path: &[Boolean],
    ) -> Result<(), SynthesisError>
    where
        A: FnOnce() -> AR,
        AR: Into<String>;
}

#[derive(Clone)]
pub enum BinaryApexCommitment<E: Engine> {
    Leaf(AllocatedNum<E>),
    Branch(Box<BinaryApexCommitment<E>>, Box<BinaryApexCommitment<E>>),
}

impl<E: Engine> BinaryApexCommitment<E> {
    fn at_path<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        path: &[Boolean],
    ) -> Result<AllocatedNum<E>, SynthesisError> {
        let length = path.len();

        match self {
            BinaryApexCommitment::Leaf(allocated_num) => {
                assert_eq!(length, 0, "Path too long for BinaryCommitment size.");

                Ok((*allocated_num).clone())
            }
            BinaryApexCommitment::Branch(left_boxed, right_boxed) => {
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
                    (BinaryApexCommitment::Leaf(left), BinaryApexCommitment::Leaf(right)) => {
                        (left, right)
                    }
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
}

impl<E: Engine> ApexCommitment<E> for BinaryApexCommitment<E> {
    #[allow(dead_code)]
    fn new(allocated_nums: &[AllocatedNum<E>]) -> Self {
        let commitments = allocated_nums;

        let size = allocated_nums.len();
        assert!(size > 0, "BinaryCommitment must not be empty.");

        if size == 1 {
            return BinaryApexCommitment::Leaf(commitments[0].clone());
        }

        assert_eq!(
            size.count_ones(),
            1,
            "BinaryCommitment size must be a power of two."
        );

        let half_size = size / 2;
        let left = Self::new(&commitments[0..half_size]);
        let right = Self::new(&commitments[half_size..]);

        BinaryApexCommitment::Branch(Box::new(left), Box::new(right))
    }

    // Initial recursive implementation of `includes` which generates (too) many constraints.
    fn includes<A, AR, CS: ConstraintSystem<E>>(
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

pub struct FlatApexCommitment<E: Engine> {
    allocated_nums: Vec<AllocatedNum<E>>,
}

impl<E: Engine> ApexCommitment<E> for FlatApexCommitment<E> {
    fn new(allocated_nums: &[AllocatedNum<E>]) -> Self {
        assert_eq!(allocated_nums.len().count_ones(), 1);
        FlatApexCommitment::<E> {
            allocated_nums: allocated_nums.to_vec(),
        }
    }

    fn includes<A, AR, CS: ConstraintSystem<E>>(
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
        let size = self.allocated_nums.len();

        if path.is_empty() {
            assert_eq!(size, 1);

            Ok(equal(cs, annotation, num, &self.allocated_nums[0]))
        } else {
            let reduced_size = size / 2; // Must divide evenly because size must be power of 2.
            let mut new_allocated = Vec::with_capacity(reduced_size);
            let curr_is_right = &path[0];
            let mut cs = &mut cs.namespace(|| {
                format!(
                    "path-{}",
                    if curr_is_right.get_value().unwrap() {
                        "1"
                    } else {
                        "0"
                    }
                )
            });

            for i in 0..reduced_size {
                let left = &self.allocated_nums[i];
                let right = &self.allocated_nums[i + reduced_size];
                let (xl, _xr) = num::AllocatedNum::conditionally_reverse(
                    cs.namespace(|| {
                        format!(
                            "conditional reversal of FlatBinaryCommitment elements ({})",
                            i
                        )
                    }),
                    &left,
                    &right,
                    &curr_is_right,
                )?;

                new_allocated.push(xl);
            }

            let reduced_apex = FlatApexCommitment::new(&new_allocated);

            reduced_apex.includes(&mut cs, annotation, num, &path[1..])
        }
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

    fn test_apex_commitment_circuit<T: ApexCommitment<Bls12>>() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let max_len = 8;

        for n in 0..max_len {
            let size = 1 << n;
            let mut outer_cs = TestConstraintSystem::<Bls12>::new();
            let mut nums = Vec::with_capacity(size);
            for i in 0..size {
                let val: <Bls12 as Engine>::Fr = rng.gen();
                let cs = &mut outer_cs.namespace(|| format!("num-{}", i));
                let num = AllocatedNum::alloc(cs, || Ok(val)).unwrap();

                nums.push(num);
            }

            let bc = T::new(&nums);

            for (i, num) in nums.iter().enumerate() {
                let mut starting_constraints = outer_cs.num_constraints();
                {
                    let cs = &mut outer_cs.namespace(|| format!("test index {}", i));
                    let path = path_from_index(cs, i, n);

                    bc.includes(cs, || format!("apex inclusion check {}", i), num, &path)
                        .unwrap();
                }
                let num_constraints = outer_cs.num_constraints() - starting_constraints;
                // length, size: constraints
                //  0,   1: 1
                //  1,   2: 4
                //  2,   4: 9
                //  3,   8: 18
                //  4,  16: 35
                //  5,  32: 68
                //  6,  64: 133
                //  7, 128: 262
                //  This is (2 * size + length) - 1 = (2^L + L) - 1.
                let expected_inclusion_constraints = (2 * size + n) - 1;
                assert_eq!(num_constraints, expected_inclusion_constraints);
                starting_constraints = num_constraints;
            }

            assert_eq!(outer_cs.num_constraints(), constraints(n));
            assert!(outer_cs.is_satisfied(), "constraints not satisfied");
        }
    }

    #[test]
    fn binary_commitment_circuit() {
        test_apex_commitment_circuit::<BinaryApexCommitment<Bls12>>();
    }

    #[test]
    fn flat_commitment_circuit() {
        test_apex_commitment_circuit::<FlatApexCommitment<Bls12>>();
    }

}
