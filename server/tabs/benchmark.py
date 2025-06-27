import streamlit as st
from streamlit import session_state as sts
import json
import traceback

from benchmark_utils import BenchmarkEvaluator
from serv_utils import preview_text, lean_code_button
from logging_utils import log_write, load_env

st.warning("Under Constuction: This page is not fully functional yet. Please check back later.")

st.title("Benchmarking LeanAide")
st.write("Here you can benchmark the performace of Lean Code generated Using LeanAide vs raw LLM output.")
st.info("You can enter a single theorem and proof, or a dataset of theorems and proofs in JSON format.")

st.subheader("Input Dataset", divider =True)

load_env()

sts.bm_input_opt = st.radio("Dataset Type", options = ["JSON Dataset", "Single Input"], index=0 if sts.bm_input_opt == "JSON Dataset" else 1, horizontal = True)
if sts.bm_input_opt == "JSON Dataset":
    uploaded_file = st.file_uploader(
        "Upload a JSON file containing a dataset of theorems and proofs.",
        type=["json"],
    )

    if uploaded_file:
        sts.bm_json_dataset = json.load(uploaded_file)
        st.success(f"Dataset loaded successfully!\nNumber of Problems in dataset: {len(sts.bm_json_dataset)}")
    else:
        sts.bm_json_dataset = {}
        st.warning("Please upload a JSON file containing a dataset of theorems and proofs.")

else:
    sts.bm_single_thm = st.text_area(
        "Enter theorem",
        placeholder="Enter a theorem here...",
        value = sts.get("bm_single_thm", ""),
    )
    if sts.bm_single_thm:
        _code_suffix = "..." if len(sts.bm_single_thm) > 50 else ""
        st.success(f"Theorem received successfully: {sts.bm_single_thm[:50]}..." + _code_suffix)
    preview_text("bm_single_thm", usage = "benchmark_thm", caption = "Theorem")

    sts.bm_single_proof = st.text_area(
        "Enter proof",
        placeholder="Enter a proof here...",
        value = sts.get("bm_single_proof", ""),
    )
    if sts.bm_single_proof:
        _code_suffix = "..." if len(sts.bm_single_proof) > 50 else ""
        st.success(f"Proof received successfully: {sts.bm_single_proof[:50]}..." + _code_suffix)
    preview_text("bm_single_proof", usage = "benchmark_pf", caption = "Proof")

st.subheader("Evaluation", divider = True)
st.info("The LLM provided in the sidebar API Credentials will be used for the benchmark. Please ensure it is set up correctly.")

if "bm_results" not in sts:
    sts.bm_results = {}
if "bm_current_progress" not in sts:
    sts.bm_current_progress = 0
if "bm_total_problems" not in sts:
    sts.bm_total_problems = len(sts["bm_json_dataset"]) if sts.bm_input_opt == "JSON Dataset" else 1

def run_benchmark():
    # Initialize/reset progress
    sts.bm_evaluator = BenchmarkEvaluator(
        llm_provider=sts.get("llm_provider", "openai"),
        model=sts.get("model_text", "o4-mini")
    )
    # Create progress bar and status placeholder
    sts.bm_total_problems = len(sts["bm_json_dataset"]) if sts.bm_input_opt == "JSON Dataset" else 1
    if not sts.bm_started:
        sts.bm_progress_bar = st.progress(0)
        sts.bm_status_text = st.empty()
        sts.bm_result_container = st.empty()  # Dynamic results display
    else:
        sts.bm_progress_bar = sts.get("bm_progress_bar", st.progress(0))
        sts.bm_status_text = sts.get("bm_status_text", st.empty())
        sts.bm_result_container = sts.get("bm_result_container", st.empty())

    _update_ui("Starting")

    try:
        print("Initializing benchmark with JSON dataset...")
        log_write("Benchmark", "Initializing benchmark with JSON dataset...")
        if sts.bm_input_opt == "JSON Dataset":
            # Process each problem in the dataset
            for idx in sts.bm_json_dataset:
                problem = sts.bm_json_dataset[idx]
                if not problem["theorem"]:
                    print(f"Skipping problem {idx} due to missing theorem.")
                    idx = int(idx) + 1 
                    continue

                # result_ai should be a lean code
                # Update session state and UI
                print("Running for Problem - LeanAide: ", idx)
                _update_ui("Running LeanAide and LLM:")
                result = sts.bm_evaluator.run_ln_llm(
                    theorem=problem["theorem"],
                    proof=problem["proof"] 
                )
                print(f"Result for Problem - AI: {idx}")
                sts.bm_results[idx] = {
                    "problem": problem["theorem"],
                    "proof": problem["proof"], 
                    "time_taken_ln": result["time_taken_ln"],
                    "result_ln": result["result_ln"],
                    "time_taken_ai": result["time_taken_ai"],
                    "result_ai": result["result_ai"],
                }
                sts.bm_current_progress = int(idx)
                _update_ui("Done with Problem")
        else:
            # Single input case
            _update_ui("Running LeanAide and LLM:")
            result = sts.bm_evaluator.run_ln_llm(
                theorem=sts.bm_single_thm,
                proof=sts.bm_single_proof
            )
            sts.bm_results[0] = {
                "problem": sts.bm_single_thm,
                "proof": sts.bm_single_proof,
                "time_taken_ln": result["time_taken_ln"],
                "result_ln": result["result_ln"],
                "time_taken_ai": result["time_taken_ai"],
                "result_ai": result["result_ai"],
            }
            _update_ui("Done with Problem")

        st.success("Benchmark completed successfully!")
        sts.bm_result_success = True
    except Exception as e:
        st.error(f"Error during benchmark: {str(e)}")
        print(traceback.format_exc())
        sts.bm_result_success = False
    finally:
        return sts.bm_results

def bm_display_results(): 
    for idx in sts.bm_results:
        result_data = sts.bm_results[idx]
        # print(result_data)
        # Show result_data in a formatted way
        st.markdown(f"### Problem: {sts.bm_current_progress}")

        # Timing table
        head_timetable = ["LeanAide Time (s)", "LLM Time (s)"] 
        time_table = [str(result_data["time_taken_ln"]), str(result_data["time_taken_ai"])]
        markdown_time_table = "| " + " | ".join(head_timetable) + " |\n"
        markdown_time_table += "| " + " | ".join(["---"] * len(head_timetable)) + " |\n"
        markdown_time_table += "| " + " | ".join(time_table) + " |\n  "

        # Print output
        st.markdown(f"**LeanAide Lean Code:**\n```lean\n{result_data['result_ln']}\n```")
        lean_code_button("bm_results", "results_ln", f"bm_lean_code_{idx}")
        st.markdown(f"**LLM Lean Code:**\n```lean\n{result_data['result_ai']}\n```")
        lean_code_button("bm_results", "results_ai", f"bm_llm_code_{idx}")
        st.markdown(markdown_time_table)
        st.markdown("---")  # Separator for each

def _update_ui(ongoing_task: str = ""):
    """Helper to update Streamlit UI components."""
    progress = sts.bm_current_progress / sts.bm_total_problems
    st.toast(sts.bm_started)
    sts.bm_progress_bar.progress(progress)
    sts.bm_status_text.markdown(f"**Progress:** {sts.bm_current_progress}/{sts.bm_total_problems} {ongoing_task}")

    # Display results incrementally
    with sts.bm_result_container.container():
        bm_display_results()

# Button trigger
sts.bm_run_button = st.button("Run Benchmark")
if sts.bm_run_button or sts.bm_started:
    if sts.bm_json_dataset or (sts.bm_single_thm and sts.bm_single_proof):
        with st.spinner("Running benchmark..."):
            st.warning("Please Donot Refresh or leave the page while the benchmark is running.")
            sts.bm_results = run_benchmark()
            sts.bm_started = True
    else:
        sts.bm_started = False
        st.warning("Please upload a dataset or enter a single theorem and proof before running the benchmark.")

if sts.bm_results and sts.bm_result_success:
    st.header("Benchmark Results", divider=True)
    st.success("Benchmark completed successfully!")
    bm_display_results()

# Convert results to JSON and download
if sts.bm_results:
    st.download_button(
        label="Download Results",
        data=json.dumps(sts.bm_results, indent=4),
        file_name= "benchmark_results.json",
        mime="application/json"
    )
