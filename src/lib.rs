#![feature(box_syntax, box_patterns)]

extern crate bellman;
extern crate pairing;
extern crate rand;

use std::fmt;

// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// Bring in some tools for using pairing-friendly curves
use pairing::{Engine, Field, PrimeField};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use pairing::bls12_381::Bls12;

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
};

use std::collections::HashMap;

// data structure to hold a FieldElement variable with its value
// it's fine to clone these
#[derive(Clone)]
struct AssignedVariable<E: Engine> {
    variable: Variable,
    value: E::Fr,
}

impl<E: Engine> fmt::Debug for AssignedVariable<E> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

#[derive(Clone)]
struct AssignedLinearCombination<E: Engine> {
    combination: LinearCombination<E>,
    value: E::Fr,
}

impl<E: Engine> From<AssignedVariable<E>> for AssignedLinearCombination<E> {
    fn from(assigned_variable: AssignedVariable<E>) -> Self {
        AssignedLinearCombination {
            combination: LinearCombination::zero() + assigned_variable.variable,
            value: assigned_variable.value,
        }
    }
}

// data structures for a program
// we don't want to clone these as they contain strings
struct Program<E: Engine> {
    main: Function<E>,
    functions: Vec<Function<E>>,
    inputs: Vec<E::Fr>,
}

struct Function<E: Engine> {
    id: String,
    input_count: usize,
    output_count: usize,
    calls: Vec<Call<E>>,
}

struct ExternalCall {
    id: String, // the function to call
    input_wires: Vec<usize>,
    output_wires: Vec<usize>,
}

struct SolverCall<E: Engine> {
    solve: Box<Fn(&HashMap<usize, AssignedVariable<E>>) -> Vec<E::Fr>>,
    output_indices: Vec<usize>,
}

impl<E: Engine> SolverCall<E> {
    fn apply<CS: ConstraintSystem<E>>(
        &self,
        witness: &mut HashMap<usize, AssignedVariable<E>>,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let output_values = (self.solve)(&witness);

        // create new variables in the CS, delegating specifying their value to the witness we're populating
        for (i, index) in self.output_indices.iter().enumerate() {
            let out = cs.alloc(|| "res", || Ok(output_values[i])).unwrap();
            witness.insert(
                *index,
                AssignedVariable {
                    variable: out,
                    value: output_values[i],
                },
            );
        }

        Ok(())
    }
}

struct ResolvedCall<E: Engine> {
    solver_call: SolverCall<E>,
    constraints: Vec<(
        Vec<(usize, E::Fr)>,
        Vec<(usize, E::Fr)>,
        Vec<(usize, E::Fr)>,
    )>,
}

enum Call<E: Engine> {
    Resolved(ResolvedCall<E>),
    External(ExternalCall),
}

impl<E: Engine> Call<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        witness: &mut HashMap<usize, AssignedVariable<E>>,
        context: &Vec<Function<E>>,
    ) -> Result<(), SynthesisError> {
        match self {
            Call::Resolved(e) => e.synthesize(cs, witness),
            Call::External(e) => e.synthesize(cs, witness, context),
        }
    }
}

impl<E: Engine> ResolvedCall<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        witness: &mut HashMap<usize, AssignedVariable<E>>,
    ) -> Result<(), SynthesisError> {
        // add outputs to constraint system and witness
        self.solver_call.apply(witness, cs)?;

        // constraints are denominated in canonical index, find the corresponding variables
        for (a, b, c) in self.constraints.clone() {
            let a = a
                .iter()
                .fold(LinearCombination::zero(), |acc, (var_index, mult)| {
                    acc + (*mult, witness.get(&var_index).unwrap().variable)
                });
            let b = b
                .iter()
                .fold(LinearCombination::zero(), |acc, (var_index, mult)| {
                    acc + (*mult, witness.get(&var_index).unwrap().variable)
                });
            let c = c
                .iter()
                .fold(LinearCombination::zero(), |acc, (var_index, mult)| {
                    acc + (*mult, witness.get(&var_index).unwrap().variable)
                });

            cs.enforce(|| "a = b * c", |lc| lc + &a, |lc| lc + &b, |lc| lc + &c);
        }

        Ok(())
    }
}

impl ExternalCall {
	fn synthesize<E: Engine, CS: ConstraintSystem<E>>(
		&self, 
		cs: &mut CS,
		witness: &mut HashMap<usize, AssignedVariable<E>>,
		context: &Vec<Function<E>>,
	) -> Result<(), SynthesisError> {
		match context.iter().find(|f| f.id == self.id) {
			Some(fun) => {
				// call function f, giving self.input_wires as inputs and defining self.output_wires as outputs
				let new_witness = fun.flatten(
					cs,
					&self.input_wires.iter().map(|wire| witness.get(&wire).unwrap().value).collect(),
					&vec![],
				).unwrap();

				// link new witness to witness using output indices

				for (index, i) in self.output_wires.iter().enumerate() {
					let output = &new_witness[index];
					witness.insert(*i, output.clone());
					// constrain

					let new_output = cs.alloc(|| "new output", || Ok(output.value)).unwrap();
					cs.enforce(|| "function call output binding", 
						|lc| lc + output.variable,
						|lc| lc + CS::one(),
						|lc| lc + new_output
					);
				}

				Ok(())
			},
			None => {
				Err(SynthesisError::AssignmentMissing)
			}
		}
	}
}

impl<E: Engine> Function<E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        arguments: &Vec<E::Fr>,
        context: &Vec<Function<E>>,
    ) -> Result<Vec<AssignedVariable<E>>, SynthesisError> {
        assert_eq!(arguments.len(), self.input_count);

        // initialise the constraint system
        let mut cs = &mut cs.namespace(|| format!("{}", self.id));

        // initialise a witness
        let mut witness: HashMap<usize, AssignedVariable<E>> = HashMap::new();

        // insert 1 constant
        witness.insert(
            0,
            AssignedVariable {
                variable: CS::one(),
                value: E::Fr::one(),
            },
        );

        // pass the inputs
        for (index, arg) in arguments.iter().enumerate() {
            let arg_variable = cs.alloc(|| "input", || Ok(*arg)).unwrap();
            witness.insert(
                index + 1,
                AssignedVariable {
                    variable: arg_variable,
                    value: *arg,
                },
            );
        }

        for call in self.calls.iter() {
            call.synthesize(&mut cs, &mut witness, &context)?;
        }

        let output_assigned_vars = (0..self.output_count)
	        .map(|index| 
	            witness.get(&(index + self.input_count + 1)).unwrap().clone()
	        ).collect();

        Ok(output_assigned_vars)
    }
}

impl<E: Engine> Circuit<E> for Program<E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        match self.main.flatten(cs, &self.inputs, &self.functions) {
            Ok(outputs) => {
                println!(
                    "Only the output: {:?}",
                    outputs
                );
                Ok(())
            }
            Err(e) => Err(e),
        }
    }
}

fn number_to_fr<E: Engine>(number: usize) -> E::Fr {
    E::Fr::from_str(&number.to_string()).unwrap()
}

#[test]
fn empty_program() {
    let rng = &mut thread_rng();

    // our toy program
    // def main():
    //    return

    let program = Program {
        main: Function {
            id: "main".to_string(),
            input_count: 0,
            output_count: 0,
            calls: vec![],
        },
        functions: vec![],
        inputs: vec![],
    };

    println!("Creating parameters...");

    let params = generate_random_parameters::<Bls12, _, _>(program, rng).unwrap();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_vec = vec![];

    // Create an instance of our circuit (pass inputs, they were not needed for the setup)
    let computation = Program {
        main: Function {
            id: "main".to_string(),
            input_count: 0,
            output_count: 0,
            calls: vec![],
        },
        functions: vec![],
        inputs: vec![],
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(verify_proof(&pvk, &proof, &[]).unwrap());
}

#[test]
fn copy_program() {
    let rng = &mut thread_rng();

    // our toy program
    // def main(private a):
    //    b = a
    //	  c = b
    //    d = c
    //    return d

    let program = Program {
        main: Function {
            id: "main".to_string(),
            input_count: 1,  // witness[1] is an input
            output_count: 1, // witness[2] is an output
            calls: vec![
                Call::Resolved(ResolvedCall {
                    solver_call: SolverCall {
                        solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
                            vec![(*witness).get(&1).unwrap().value]
                        }),
                        output_indices: vec![4],
                    },
                    constraints: vec![(
                        vec![(0, number_to_fr::<Bls12>(1))],
                        vec![(1, number_to_fr::<Bls12>(1))],
                        vec![(4, number_to_fr::<Bls12>(1))],
                    )],
                }),
                Call::Resolved(ResolvedCall {
                    solver_call: SolverCall {
                    	solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
                            vec![(*witness).get(&4).unwrap().value]
                        }),
                        output_indices: vec![3],
                    },
                    constraints: vec![(
                        vec![(0, number_to_fr::<Bls12>(1))],
                        vec![(4, number_to_fr::<Bls12>(1))],
                        vec![(3, number_to_fr::<Bls12>(1))],
                    )],
                }),
                Call::Resolved(ResolvedCall {
                    solver_call: SolverCall {
                    	solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
                            vec![(*witness).get(&3).unwrap().value]
                        }),
                        output_indices: vec![2],
                    },
                    constraints: vec![(
                        vec![(0, number_to_fr::<Bls12>(1))],
                        vec![(3, number_to_fr::<Bls12>(1))],
                        vec![(2, number_to_fr::<Bls12>(1))],
                    )],
                }),
            ],
        },
        functions: vec![],
        inputs: vec![number_to_fr::<Bls12>(42)],
    };

    println!("Creating parameters...");

    let params = generate_random_parameters::<Bls12, _, _>(program, rng).unwrap();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_vec = vec![];

    // Create an instance of our circuit (pass inputs, they were not needed for the setup)
    let computation = Program {
        main: Function {
            id: "main".to_string(),
            input_count: 1,  // witness[1] is an input
            output_count: 1, // witness[2] is an output
            calls: vec![
                Call::Resolved(ResolvedCall {
                    solver_call: SolverCall {
                        solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
                            vec![(*witness).get(&1).unwrap().value]
                        }),
                        output_indices: vec![4],
                    },
                    constraints: vec![(
                        vec![(0, number_to_fr::<Bls12>(1))],
                        vec![(1, number_to_fr::<Bls12>(1))],
                        vec![(4, number_to_fr::<Bls12>(1))],
                    )],
                }),
                Call::Resolved(ResolvedCall {
                    solver_call: SolverCall {
                    	solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
                            vec![(*witness).get(&4).unwrap().value]
                        }),
                        output_indices: vec![3],
                    },
                    constraints: vec![(
                        vec![(0, number_to_fr::<Bls12>(1))],
                        vec![(4, number_to_fr::<Bls12>(1))],
                        vec![(3, number_to_fr::<Bls12>(1))],
                    )],
                }),
                Call::Resolved(ResolvedCall {
                    solver_call: SolverCall {
                    	solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
                            vec![(*witness).get(&3).unwrap().value]
                        }),
                        output_indices: vec![2],
                    },
                    constraints: vec![(
                        vec![(0, number_to_fr::<Bls12>(1))],
                        vec![(3, number_to_fr::<Bls12>(1))],
                        vec![(2, number_to_fr::<Bls12>(1))],
                    )],
                }),
            ],
        },
        functions: vec![],
        inputs: vec![number_to_fr::<Bls12>(42)],
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(verify_proof(&pvk, &proof, &[]).unwrap());
}

#[test]
fn external_call_program() {
    let rng = &mut thread_rng();

    // our toy program
    // def main(private a):
    //    b = foo(a)
    //	  return b

    let program = Program {
        main: Function {
            id: "main".to_string(),
            input_count: 1,  // witness[1] is an input
            output_count: 1, // witness[2] is an output
            calls: vec![
                Call::External(ExternalCall {
                	id: "foo".to_string(),
                	input_wires: vec![1],
                	output_wires: vec![2]
                }),
            ],
        },
        functions: vec![
        	Function {
	            id: "foo".to_string(),
	            input_count: 1,  // witness[1] is an input
	            output_count: 1, // witness[2] is an output
	            calls: vec![
	                Call::Resolved(ResolvedCall {
	                    solver_call: SolverCall {
	                    	solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
	                            vec![(*witness).get(&1).unwrap().value]
	                        }),
	                        output_indices: vec![2],
	                    },
	                    constraints: vec![(
	                        vec![(0, number_to_fr::<Bls12>(1))],
	                        vec![(1, number_to_fr::<Bls12>(1))],
	                        vec![(2, number_to_fr::<Bls12>(1))],
	                    )],
	                })
	            ],
	        }
        ],
        inputs: vec![number_to_fr::<Bls12>(42)],
    };

    println!("Creating parameters...");

    let params = generate_random_parameters::<Bls12, _, _>(program, rng).unwrap();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_vec = vec![];

    // Create an instance of our circuit (pass inputs, they were not needed for the setup)
    let computation = Program {
        main: Function {
            id: "main".to_string(),
            input_count: 1,  // witness[1] is an input
            output_count: 1, // witness[2] is an output
            calls: vec![
                Call::External(ExternalCall {
                	id: "foo".to_string(),
                	input_wires: vec![1],
                	output_wires: vec![2]
                }),
            ],
        },
        functions: vec![
        	Function {
	            id: "foo".to_string(),
	            input_count: 1,  // witness[1] is an input
	            output_count: 1, // witness[2] is an output
	            calls: vec![
	                Call::Resolved(ResolvedCall {
	                    solver_call: SolverCall {
	                    	solve: Box::new(|witness: &HashMap<usize, AssignedVariable<Bls12>>| {
	                            vec![(*witness).get(&1).unwrap().value]
	                        }),
	                        output_indices: vec![2],
	                    },
	                    constraints: vec![(
	                        vec![(0, number_to_fr::<Bls12>(1))],
	                        vec![(1, number_to_fr::<Bls12>(1))],
	                        vec![(2, number_to_fr::<Bls12>(1))],
	                    )],
	                })
	            ],
	        }
        ],
        inputs: vec![number_to_fr::<Bls12>(42)],
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(verify_proof(&pvk, &proof, &[]).unwrap());
}