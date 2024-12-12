use std::{fs, path::Path};

use stone_prover_sdk::{
    cairo_vm::{extract_execution_artifacts, run_in_proof_mode, ExecutionArtifacts},
    error::{ProverError, VerifierError},
    fri::generate_prover_parameters,
    json::{read_json_from_file, write_json_to_file},
    models::{Layout, ProverConfig, PublicInput, Verifier},
    prover::{run_prover, run_prover_from_command_line},
    verifier::run_verifier,
};

/// Given a layout and a compiled Cairo Zero program,
/// Generate a proof of the correct execution of that program and verify the proof.
///
/// This function expects some naming conventions:
/// The Cairo Zero program must compiled in Proof mode, `--proof_mode` flag,
/// and the output should `--output my_prgm.proof_mode.json`.
///
/// It executes the compiled program with the Rust CairoVM (cairo-vm),
/// extracts the public input, the private input (witness) along the trace and the memory.
///
/// Then, it generates the parameters for the prover based on the number of steps and the targeted verifier (Stone or L1).
///
/// The Configuration of the prover is the default one.
///
/// It runs the Stone prover through its CLI: `cpu_air_prover`.
///
/// Then it runs the Stone verifier through its CLI as well: `cpu_air_verifier`.
///
/// All the intermediary artifacts (AIR Public Input, AIR Private Input, Encoded trace and memory) are in a temporary folder.
///
/// The proof as well, but we also write it in the folder where the Cairo Zero compilation artifacts are read, allowing us to check the proof.
fn run_sdk(
    do_verif: bool,
    layout: Layout,
    filename_base: String,
) -> (Result<(), ProverError>, Result<(), VerifierError>) {
    let program_path = filename_base.clone() + ".proof_mode.json";
    let output_proof = filename_base + ".proof.json";

    let program = fs::read(program_path).unwrap();

    let (runner, vm) = run_in_proof_mode(&program, layout, None).unwrap();

    // Prover Configuration File
    let execution_resources = runner.get_execution_resources(&vm).unwrap();

    let ExecutionArtifacts {
        public_input,
        private_input,
        memory,
        trace,
    } = extract_execution_artifacts(runner, vm).unwrap();

    let parameters =
        generate_prover_parameters(execution_resources.n_steps as u32, Verifier::Stone);

    // Prover Config File
    let prover_config = ProverConfig::default();

    let proof_result = run_prover(
        &public_input,
        &private_input,
        &memory,
        &trace,
        &prover_config,
        &parameters,
    );

    let proof = proof_result.as_ref().unwrap();
    let _ = write_json_to_file(proof, &output_proof).unwrap();

    let verifier = if do_verif {
        run_verifier(&Path::new(&output_proof))
    } else {
        Ok(())
    };

    let proof_result = proof_result.map(|_| ());
    (proof_result, verifier)
}

/// Given all inputs required by the Stone prover,
/// generate a proof of the correct execution of the corresponding program and verify it.
///
/// This function expects some naming conventions:
/// - All the files should have the same name (e.g. my_prgm.trace, my_prgm.memory)
/// - AIR Public Input extension: `.air_public_input.json`
/// - AIR Private Input extension: `.air_private_input.json`
/// - Trace: `.trace`
/// - Memory: `.memory`
///
/// It generates the parameters for the prover based on the number of steps in the AIR public input.
///
/// The Configuration of the prover is the default one.
///
/// It runs the Stone prover through its CLI: `cpu_air_prover`.
///
/// Then it runs the Stone verifier through its CLI as well: `cpu_air_verifier`.
fn run_filename_from_command_line(
    do_verif: bool,
    filename_base: String,
) -> (Result<(), ProverError>, Result<(), VerifierError>) {
    let air_public_filename = filename_base.clone() + ".air_public_input.json";
    let air_private_filename = filename_base.clone() + ".air_private_input.json";
    let prover_parameters_filename = filename_base.clone() + ".prover_parameters.json";
    let output_proof = filename_base + ".proof.json";

    // AIR Public Input
    let public_input: PublicInput = read_json_from_file(air_public_filename.clone()).unwrap();

    // Prover Parameters
    let parameters = generate_prover_parameters(public_input.n_steps, Verifier::Stone);
    let _ = write_json_to_file(parameters, prover_parameters_filename.clone()).unwrap();

    let proof = run_prover_from_command_line(
        Path::new(&air_public_filename),
        Path::new(&air_private_filename),
        Path::new("prover_config.json"),
        Path::new(&prover_parameters_filename),
        Path::new(&output_proof),
    );

    let verifier = if do_verif {
        run_verifier(&Path::new(&output_proof))
    } else {
        Ok(())
    };

    (proof, verifier)
}

fn run_prover_verifier(
    use_sdk: bool,
    do_verif: bool,
    layout: Option<Layout>,
    filename_base: String,
) {
    let (proof, verifier) = if use_sdk {
        run_sdk(do_verif, layout.unwrap(), filename_base)
    } else {
        run_filename_from_command_line(do_verif, filename_base)
    };

    println!("Proof correctly generated: {}", proof.is_ok());
    if proof.is_err() {
        println!("Proof Error: {:#?}", proof);
    }

    if do_verif {
        println!("Proof correctly verified: {}", verifier.is_ok());
    }
}

fn main() {
    let filename_base =
        String::from("cairo/test_rlp/test_rlp_encode_u256__1733936539732489000_841a7ee0");
    let layout = Some(Layout::StarknetWithKeccak);
    run_prover_verifier(false, false, layout, filename_base);
}

#[cfg(test)]
mod tests {
    use crate::{run_filename_from_command_line, run_sdk};
    use stone_prover_sdk::models::Layout;

    const DO_VERIF: bool = true;

    #[test]
    fn test_rlp_all_cairo() {
        let (proof, verifier) = run_filename_from_command_line(
            DO_VERIF,
            String::from("cairo/test_rlp/test_rlp_encode_u256__1733851371118308000_841a7ee0"),
        );

        println!("{:?}", proof.as_ref().unwrap());
        println!("{:?}", verifier.as_ref().unwrap());

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]

    fn test_rlp_starknet_with_keccak() {
        let (proof, verifier) = run_filename_from_command_line(
            DO_VERIF,
            String::from("cairo/test_rlp/test_rlp_encode_u256__1733936539732489000_841a7ee0"),
        );

        println!("{:?}", proof.as_ref().unwrap());
        println!("{:?}", verifier.as_ref().unwrap());

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_fibonacci_plain() {
        let (proof, verifier) = run_sdk(DO_VERIF, Layout::Plain, String::from("cairo/fib/fib"));

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_fibonacci_small() {
        let (proof, verifier) = run_sdk(DO_VERIF, Layout::Small, String::from("cairo/fib/fib"));

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_fibonacci_all_cairo() {
        let (proof, verifier) = run_sdk(DO_VERIF, Layout::AllCairo, String::from("cairo/fib/fib"));

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_factorial_small() {
        let (proof, verifier) = run_sdk(
            DO_VERIF,
            Layout::Small,
            String::from("cairo/factorial/factorial"),
        );

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_factorial_starknet() {
        let (proof, verifier) = run_sdk(
            DO_VERIF,
            Layout::Starknet,
            String::from("cairo/factorial/factorial"),
        );

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_integration_starknet() {
        let (proof, verifier) = run_sdk(
            DO_VERIF,
            Layout::Starknet,
            String::from("cairo/integration/integration"),
        );

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_keccak_starknet_with_keccak() {
        let (proof, verifier) = run_sdk(
            DO_VERIF,
            Layout::StarknetWithKeccak,
            String::from("cairo/keccak_builtin/keccak_builtin"),
        );

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_circuit_all_cairo() {
        let (proof, verifier) =
            run_filename_from_command_line(DO_VERIF, String::from("cairo/circuit/circuit"));

        println!("{:?}", proof.as_ref().unwrap());

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }

    #[test]
    fn test_apply_poly_all_cairo() {
        let (proof, verifier) =
            run_filename_from_command_line(DO_VERIF, String::from("cairo/apply_poly/apply_poly"));

        println!("{:?}", proof.as_ref().unwrap());

        assert!(proof.is_ok());
        assert!(verifier.is_ok());
    }
}
