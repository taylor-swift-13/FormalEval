#!/usr/bin/env python3
"""
Batch negative proof: Read negative testcases from negative.jsonl,
read spec from negative/input/{TYPE},
generate proof for each negative testcase.
Only if all proofs fail is it considered good (spec is robust).

Supports:
- Single spec processing (--spec-id)
- Batch processing (--range START:END)
- Underscore filenames (e.g., 1_.v)
- Multi-threaded parallel processing (--num-workers N)
"""

import argparse
import json
import os
import re
import sys
import subprocess
import tempfile
import shutil
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Tuple, Dict, Any, Optional

from config import MODEL_NAME, LLMConfig, TYPE
from llm import Chatbot
from logger import get_logger

# Mutation JSONL file path (hardcoded)
NEGATIVE_JSONL_PATH = "negative/negative_cases.jsonl"
# LLM model used for proof generation (hardcoded)
LLM_MODEL = "gemini-3-pro-preview"


def load_negative_jsonl(jsonl_path: str) -> Dict[int, List[Dict[str, Any]]]:
    """
    Load negative testcases from negative.jsonl.
    
    Returns:
        dict: {spec_id: [testcase1, testcase2, ...]}
    """
    negatives = {}
    with open(jsonl_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
                spec_id = data.get('id')
                testcases = data.get('testcases', [])
                if spec_id is not None:
                    negatives[spec_id] = testcases
            except json.JSONDecodeError as e:
                print(f"Warning: Failed to parse line in {jsonl_path}: {e}", file=sys.stderr)
                continue
    return negatives


def format_negative_testcase(testcase: Dict[str, Any]) -> str:
    """
    Convert negative testcase to Coq format string.
    
    Args:
        testcase: {"input": ..., "output": ...}
        
    Returns:
        Coq format test case string
    """
    def convert_value(val):
        if isinstance(val, bool):
            return "true" if val else "false"
        elif isinstance(val, int):
            return f"{val}%Z"
        elif isinstance(val, float):
            return f"{val}%R"
        elif isinstance(val, str):
            return f'"{val}"'
        elif isinstance(val, list):
            if not val:
                return "[]"
            elements = [convert_value(x) for x in val]
            return f"[{'; '.join(elements)}]"
        elif val is None:
            return "None"
        else:
            return str(val)
    
    input_val = testcase.get('input')
    output_val = testcase.get('output')
    
    # Handle case where input may be a list (multiple arguments)
    if isinstance(input_val, list):
        input_str = ", ".join(convert_value(x) for x in input_val)
    else:
        input_str = convert_value(input_val)
    
    output_str = convert_value(output_val)
    
    return f"input = {input_str}, output = {output_str}"


def call_llm_for_proof(spec_content: str, example: str, llm: Chatbot) -> str:
    """Call LLM to generate Coq proof"""
    base_prompt = f"""Please generate a complete Coq proof for the following specification and test case.

Specification definition:
{spec_content}

Test case:
{example}

First, judge whether you can generate a valid proof for the given spec and test case.
- If YES: Generate the complete Example proof (Proof steps + Qed), with any necessary imports or lemmas.
- If NO: Return only "Test case is not accepted".

Do NOT modify the given spec or test case.

Notes:
1. Use appropriate Coq tactics (such as unfold, simpl, reflexivity, lia, lra, etc.)
2. Ensure the proof is complete and correct
3. If real number operations are involved, please use R_scope
4. If integer operations are involved, please use Z_scope
5. For list operations, please use the appropriate List library functions

Please return Coq code directly, without any additional explanations:
"""

    prompt = base_prompt

    proof = llm.chat(prompt)
    
    # Remove possible code block markers
    proof = proof.strip()
    if proof.startswith('```coq'):
        proof = proof[6:]
    if proof.startswith('```'):
        proof = proof[3:]
    if proof.endswith('```'):
        proof = proof[:-3]
    proof = proof.strip()
    
    return proof


def verify_coq_proof(combined_content: str) -> Tuple[bool, str]:
    """Verify if Coq proof is correct: verify (original spec + generated proof) combined content"""
    try:
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False, encoding='utf-8') as temp_file:
            temp_file.write(combined_content)
            temp_file.flush()
            result = subprocess.run(
                ['coqtop', '-batch', '-l', temp_file.name],
                capture_output=True,
                text=True,
                timeout=30
            )
            os.unlink(temp_file.name)
            if result.returncode == 0:
                return True, ""
            else:
                return False, result.stderr + result.stdout
    except subprocess.TimeoutExpired:
        return False, "Coq verification timed out"
    except Exception as e:
        return False, f"Error during verification: {e}"


def mutate_and_prove(spec_id: str, jsonl_path: str, input_model: str, spec_input_dir: str) -> Tuple[bool, str]:
    """
    Generate proofs for all negative testcases of a single spec.
    
    Rules:
      - Read all negative testcases for this spec from negative.jsonl (using numeric part, removing underscore)
      - Read spec from negative/input/{TYPE}/{spec_id}.v (supports underscore filenames like 1_.v)
      - Generate proof for each negative testcase (using gemini-3-pro-preview model)
      - If all proofs fail -> good (spec is robust)
      - If at least one proof succeeds -> bad (spec too weak)
      
    Returns (is_good, message):
      is_good=True  means all proofs failed (good), files saved to negative/output/{type}/good/
      is_good=False means at least one proof succeeded (bad), files saved to negative/output/{type}/bad/
    """
    # Load negative testcases
    negatives = load_negative_jsonl(jsonl_path)
    # Extract numeric part from spec_id (e.g., "1" or "1_" both extract as 1)
    # Note: id in negative.jsonl is numeric (without underscore), so use numeric part to query
    numeric_id = int(re.sub(r'[^0-9]', '', spec_id)) if spec_id else 0
    
    if numeric_id not in negatives:
        return False, f"No negative testcases found for spec {spec_id} in {jsonl_path}"
    
    testcases = negatives[numeric_id]
    if not testcases:
        return False, f"Empty negative testcases for spec {spec_id}"
    
    # Read spec file (from negative/input)
    # Supports underscore filenames (e.g., 1_.v)
    spec_path = os.path.join(spec_input_dir, f"{spec_id}.v")
    if not os.path.exists(spec_path):
        return False, f"Spec file not found: {spec_path}"
    
    with open(spec_path, 'r', encoding='utf-8') as f:
        spec_content = f.read()
    
    # Mutation directory structure: negative/output/{input_model}/good and negative/output/{input_model}/bad
    # Input is in negative/input/{TYPE}, output organized by type
    negative_base_dir = os.path.join("negative", "output", input_model)
    
    negative_good_dir = os.path.join(negative_base_dir, "good")
    negative_bad_dir = os.path.join(negative_base_dir, "bad")
    os.makedirs(negative_good_dir, exist_ok=True)
    os.makedirs(negative_bad_dir, exist_ok=True)
    
    logger = get_logger(
        model_name=f"{input_model}-negative",
        spec_id=numeric_id,
        test_id=0,
        type_name="negative",
    )
    
    # Initialize LLM (using hardcoded model)
    llm_config = LLMConfig(api_model=LLM_MODEL)
    llm = Chatbot(llm_config)
    
    try:
        logger.print_section(f"[Mutation Proof] Spec {spec_id}")
        logger.info(f"Spec file: {spec_path}")
        logger.info(f"Mutation testcases count: {len(testcases)}")
        
        proof_results = []  # Store proof results for each negative testcase
        
        # Generate proof for each negative testcase
        for idx, testcase in enumerate(testcases):
            logger.print_section(f"[Mutation Testcase {idx}]")
            example_str = format_negative_testcase(testcase)
            logger.info(f"Test case: {example_str}")
            
            # Use LLM to generate proof
            logger.info(f"[Mutation] Generating proof for testcase {idx}")
            proof = call_llm_for_proof(spec_content, example_str, llm)
            
            logger.print_section(f"[Mutation] Generated Proof for Testcase {idx}")
            logger.info(proof)
            
            proof = proof.strip()
            
            # Verify proof
            is_valid, error_output = verify_coq_proof(proof)
            
            proof_results.append({
                'index': idx,
                'testcase': testcase,
                'proof': proof,
                'is_valid': is_valid,
                'error': error_output if not is_valid else ""
            })
            
            # Save each negative proof file (format: {spec_id}_{negative_index}.v)
            # Preserve original spec_id format (including possible underscore)
            output_filename = f"{spec_id}_{idx}.v"
            
            if is_valid:
                logger.info(f"✓ [Mutation Testcase {idx}] Proof is valid")
                # Save to bad directory (because proof succeeded)
                output_path = os.path.join(negative_bad_dir, output_filename)
            else:
                logger.info(f"✗ [Mutation Testcase {idx}] Proof failed")
                logger.info(f"Error: {error_output[:200]}")
                # Save to good directory (because proof failed)
                output_path = os.path.join(negative_good_dir, output_filename)
            
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(proof)
            logger.info(f"Saved to: {output_path}")
        
        # Determine result: only if all proofs fail is it considered good
        all_failed = all(not result['is_valid'] for result in proof_results)
        success_count = sum(1 for result in proof_results if result['is_valid'])
        
        logger.print_section(f"[Mutation Summary] Spec {spec_id}")
        logger.info(f"Total negative testcases: {len(testcases)}")
        logger.info(f"Successful proofs: {success_count}")
        logger.info(f"Failed proofs: {len(testcases) - success_count}")
        
        if all_failed:
            logger.info(f"✓ [Mutation] All proofs failed -> GOOD (spec is robust)")
            
            # Verify: check if all generated files are in good directory
            all_in_good = True
            missing_files = []
            for idx in range(len(testcases)):
                output_filename = f"{spec_id}_{idx}.v"
                good_file_path = os.path.join(negative_good_dir, output_filename)
                bad_file_path = os.path.join(negative_bad_dir, output_filename)
                
                if not os.path.exists(good_file_path):
                    all_in_good = False
                    missing_files.append(f"Missing in good: {output_filename}")
                if os.path.exists(bad_file_path):
                    all_in_good = False
                    missing_files.append(f"Found in bad: {output_filename}")
            
            if not all_in_good:
                logger.warning(f"⚠ [Mutation] Not all files are in good directory:")
                for msg in missing_files:
                    logger.warning(f"  {msg}")
                logger.close()
                return True, f"GOOD: All {len(testcases)} negative proofs failed, but file verification failed."
            
            # When all proofs fail and all files are in good directory (GOOD), copy input spec to negative/fail_all directory
            negative_fail_all_dir = os.path.join("negative", "fail_all", input_model)
            os.makedirs(negative_fail_all_dir, exist_ok=True)
            # Preserve original spec_id format (including possible underscore)
            dest_spec_path = os.path.join(negative_fail_all_dir, f"{spec_id}.v")
            
            # Skip if target file already exists
            if not os.path.exists(dest_spec_path):
                try:
                    shutil.copy2(spec_path, dest_spec_path)
                    logger.info(f"Copied input spec to negative/fail_all: {dest_spec_path}")
                except Exception as e:
                    logger.warning(f"Failed to copy spec to negative/fail_all: {e}")
            else:
                logger.info(f"Spec already exists in negative/fail_all: {dest_spec_path}")
            
            logger.close()
            return True, f"GOOD: All {len(testcases)} negative proofs failed. Spec is robust."
        else:
            logger.info(f"✗ [Mutation] {success_count}/{len(testcases)} proofs succeeded -> BAD (spec too weak)")
            logger.close()
            return False, f"BAD: {success_count}/{len(testcases)} negative proofs succeeded. Spec too weak."
    
    except Exception as e:
        msg = f"Error during negative proof generation for spec {spec_id}: {e}"
        logger.error(msg, exc_info=True)
        logger.close()
        return False, msg


def scan_spec_files_in_range(spec_input_dir: str, start: int, end: int) -> List[str]:
    """
    Scan directory for all spec files in specified range, including underscore files.
    If both {id}.v and {id}_.v exist, both will be processed.
    
    Args:
        spec_input_dir: Input directory path
        start: Start ID (inclusive)
        end: End ID (inclusive)
        
    Returns:
        List of spec_id strings (may be "1" or "1_" format), sorted by numeric ID
    """
    spec_ids = []
    
    if not os.path.exists(spec_input_dir):
        return []
    
    # Scan all .v files in directory
    for filename in os.listdir(spec_input_dir):
        if not filename.endswith('.v'):
            continue
        
        # Extract numeric part from filename (remove .v extension)
        base_name = filename[:-2]  # Remove .v
        
        # Extract numeric ID (remove underscore)
        numeric_id_str = re.sub(r'[^0-9]', '', base_name)
        if not numeric_id_str:
            continue
        
        try:
            numeric_id = int(numeric_id_str)
            # Check if in range
            if start <= numeric_id <= end:
                # Preserve original filename format (with or without underscore), add to list
                spec_ids.append(base_name)
        except ValueError:
            continue
    
    # Sort by numeric ID, when same numeric ID, non-underscore comes first
    spec_ids = sorted(spec_ids, key=lambda x: (int(re.sub(r'[^0-9]', '', x)), x.endswith('_')))
    return spec_ids


def main() -> None:
    parser = argparse.ArgumentParser(
        description='Generate proofs for all negative testcases of Coq specifications (based on negative.jsonl and negative/input/{TYPE})',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --range 1:10
  %(prog)s --range 1:100
        """
    )
    parser.add_argument(
        '--range',
        type=str,
        default=None,
        metavar='START:END',
        help='Process specification range, format: START:END (both START and END are inclusive, e.g., 1:10). Mutually exclusive with --spec-id'
    )
    parser.add_argument(
        '--num-workers',
        type=int,
        default=24,
        metavar='N',
        help='Number of parallel worker threads (default: 24)'
    )
    args = parser.parse_args()
    
    # Validate arguments: --spec-id and --range must and can only specify one
    if not args.range:
        parser.error("Must specify --range")
    
    # Input path: negative/input/{TYPE}
    spec_input_dir = os.path.join("negative", "input", TYPE)
    input_model = TYPE  # Use TYPE from config (for output and fail_all directories)
    
    # Determine spec_id list to process
    if args.range:
        # Batch mode: parse range and scan directory
        try:
            start, end = map(int, args.range.split(':'))
            if start > end:
                parser.error(f"Range start ({start}) must be <= end ({end})")
            # Scan directory for all files in range (including underscore files)
            spec_ids = scan_spec_files_in_range(spec_input_dir, start, end)
            if not spec_ids:
                print(f"[WARNING] No spec files found in range {start}:{end} in {spec_input_dir}", file=sys.stderr)
        except ValueError as e:
            parser.error(f'--range parameter format invalid, should be START:END (e.g., 1:10): {e}')
    
    # Process each spec_id (supports multi-threading)
    successes = []
    failures = []
    num_workers = args.num_workers
    
    if num_workers <= 1:
        # Single-threaded mode
        for spec_id in spec_ids:
            print(f"\n=== Processing spec {spec_id} ===")
            is_good, msg = mutate_and_prove(spec_id, NEGATIVE_JSONL_PATH, input_model, spec_input_dir)
            if is_good:
                print(f"[GOOD] {msg}")
                successes.append(spec_id)
            else:
                print(f"[BAD] {msg}", file=sys.stderr)
                failures.append((spec_id, msg))
    else:
        # Multi-threaded mode
        print(f"\n=== Using {num_workers} workers for parallel processing ===")
        
        def process_spec(spec_id: str) -> Tuple[str, bool, str]:
            """Wrapper function to process a single spec"""
            print(f"[Thread] Starting spec {spec_id}")
            is_good, msg = mutate_and_prove(spec_id, NEGATIVE_JSONL_PATH, input_model, spec_input_dir)
            print(f"[Thread] Finished spec {spec_id}: {'GOOD' if is_good else 'BAD'}")
            return (spec_id, is_good, msg)
        
        # Use thread pool for parallel processing
        with ThreadPoolExecutor(max_workers=num_workers) as executor:
            # Submit all tasks
            future_to_spec = {
                executor.submit(process_spec, spec_id): spec_id 
                for spec_id in spec_ids
            }
            
            # Collect results
            for future in as_completed(future_to_spec):
                spec_id = future_to_spec[future]
                try:
                    spec_id_result, is_good, msg = future.result()
                    if is_good:
                        print(f"[GOOD] Spec {spec_id_result}: {msg}")
                        successes.append(spec_id_result)
                    else:
                        print(f"[BAD] Spec {spec_id_result}: {msg}", file=sys.stderr)
                        failures.append((spec_id_result, msg))
                except Exception as e:
                    error_msg = f"Error processing spec {spec_id}: {e}"
                    print(f"[ERROR] {error_msg}", file=sys.stderr)
                    failures.append((spec_id, error_msg))
    
    # Print summary
    print(f"\n=== Summary ===")
    print(f"Total processed: {len(spec_ids)}")
    print(f"Successes (GOOD): {len(successes)}")
    print(f"Failures (BAD): {len(failures)}")
    
    if successes:
        print(f"\nSuccessful specs: {', '.join(map(str, successes))}")
    if failures:
        print(f"\nFailed specs:")
        for spec_id, msg in failures:
            print(f"  {spec_id}: {msg}")
    
    # Exit with code 1 if there are failures
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()

