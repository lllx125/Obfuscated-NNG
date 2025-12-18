#!/usr/bin/env python3
"""
Asynchronous LLM Benchmark Runner
Runs multiple LLM benchmarks in parallel with smart task distribution and unified progress reporting.
"""

import asyncio
import time
import os
import sys
from pathlib import Path
from collections import defaultdict
from typing import Dict, List, Tuple
from benchmark.query_llm import run_experiment, TARGET_DATASETS
from benchmark.debug_llm import validate_llm
from utils.discord_notify import send_msg

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

NUM_RUN = 5
START_RUN = 1
MAX_RETRY = 3
LLM_LIST = [
    "deepseek-r1",
    "gpt-4o",
    "deepseek-prover-v2"
]

# Parallel execution limits
MAX_PARALLEL_PROCESSES = 10

# Rate limits (requests per minute) for each LLM
LLM_RATE_LIMITS = {
    'gemini-flash': 10,
    'gemini-pro': 5,
    'deepseek-r1': 500,
    'gpt-4o': 480,
    'deepseek-prover-v2': 100,
}

# Dataset ordering (slowest first for optimal distribution)
# Based on typical query times: original > obfuscated_5 > obfuscated_4 > obfuscated_3 > obfuscated_2 > obfuscated_1
DATASET_ORDER_BY_SPEED = [
    "original",
    "obfuscated_5",
    "obfuscated_4",
    "obfuscated_3",
    "obfuscated_2",
    "obfuscated_1"
]

# ============================================================================
# RATE LIMITING
# ============================================================================

class RateLimiter:
    """Rate limiter that enforces requests per minute limit"""

    def __init__(self, rate_limit: int):
        """
        Args:
            rate_limit: Maximum requests per minute
        """
        self.rate_limit = rate_limit
        self.requests = []  # List of request timestamps
        self.lock = asyncio.Lock()

    async def acquire(self):
        """Wait until we can make a request without exceeding rate limit"""
        async with self.lock:
            now = time.time()

            # Remove requests older than 1 minute
            self.requests = [req_time for req_time in self.requests if now - req_time < 60]

            # If we're at the limit, wait until the oldest request expires
            if len(self.requests) >= self.rate_limit:
                oldest_request = self.requests[0]
                wait_time = 60 - (now - oldest_request) + 0.1  # Add small buffer
                if wait_time > 0:
                    await asyncio.sleep(wait_time)
                    # Clean up again after waiting
                    now = time.time()
                    self.requests = [req_time for req_time in self.requests if now - req_time < 60]

            # Record this request
            self.requests.append(time.time())

# ============================================================================
# PROGRESS TRACKING
# ============================================================================

class ProgressTracker:
    """Tracks progress across all LLM benchmarks"""

    def __init__(self):
        self.tasks: Dict[str, Dict] = {}  # task_id -> task info
        self.llm_counts: Dict[str, int] = defaultdict(int)  # llm_name -> count running
        self.start_time = time.time()
        self.lock = asyncio.Lock()

    async def register_task(self, task_id: str, llm_name: str, dataset: str, run_idx: int):
        """Register a new task"""
        async with self.lock:
            self.tasks[task_id] = {
                'llm_name': llm_name,
                'dataset': dataset,
                'run_idx': run_idx,
                'status': 'pending',
                'completed_queries': 0,
                'total_queries': 68,  # Each dataset has 68 queries
                'start_time': None
            }

    async def update_task(self, task_id: str, event_data: Dict):
        """Update task progress based on callback events"""
        async with self.lock:
            if task_id not in self.tasks:
                return

            task = self.tasks[task_id]
            event = event_data.get('event')

            if event == 'run_start':
                task['status'] = 'running'
                task['start_time'] = time.time()
            elif event == 'dataset_start':
                task['status'] = 'running'
            elif event == 'query_progress':
                task['completed_queries'] = event_data.get('query_idx', 0)
            elif event == 'dataset_complete':
                task['status'] = 'completed'
                task['completed_queries'] = task['total_queries']

    async def get_progress_report(self) -> str:
        """Generate progress report for Discord"""
        async with self.lock:
            lines = []
            lines.append("**🚀 LLM Benchmark Progress**\n")

            # Group by LLM
            llm_tasks = defaultdict(list)
            for task_id, task in self.tasks.items():
                llm_tasks[task['llm_name']].append(task)

            # Report each LLM
            for llm_name in sorted(llm_tasks.keys()):
                tasks = llm_tasks[llm_name]
                running_tasks = [t for t in tasks if t['status'] == 'running']

                total_queries = sum(t['total_queries'] for t in tasks)
                completed_queries = sum(t['completed_queries'] for t in tasks)

                # Calculate ETA
                eta_str = "N/A"
                if completed_queries > 0:
                    elapsed = time.time() - self.start_time
                    avg_time_per_query = elapsed / completed_queries
                    remaining_queries = total_queries - completed_queries
                    estimated_time_left = avg_time_per_query * remaining_queries

                    hours, remainder = divmod(int(estimated_time_left), 3600)
                    minutes, seconds = divmod(remainder, 60)

                    eta_str = ""
                    if hours > 0:
                        eta_str += f"{hours}h "
                    if minutes > 0:
                        eta_str += f"{minutes}m "
                    eta_str += f"{seconds}s"

                # Running processes indicator
                process_indicator = f" (×{len(running_tasks)})" if len(running_tasks) > 1 else ""

                lines.append(f"**{llm_name}**{process_indicator}: {completed_queries}/{total_queries} | ETA: {eta_str}")

                # Show currently running datasets
                if running_tasks:
                    running_datasets = [f"{t['dataset']}" for t in running_tasks]
                    lines.append(f"  └─ Running: {', '.join(running_datasets)}")

            # Overall stats
            all_tasks = list(self.tasks.values())
            total_all = sum(t['total_queries'] for t in all_tasks)
            completed_all = sum(t['completed_queries'] for t in all_tasks)
            progress_pct = (completed_all / total_all * 100) if total_all > 0 else 0

            elapsed = time.time() - self.start_time
            elapsed_hours, remainder = divmod(int(elapsed), 3600)
            elapsed_minutes, elapsed_seconds = divmod(remainder, 60)
            elapsed_str = f"{elapsed_hours}h {elapsed_minutes}m {elapsed_seconds}s" if elapsed_hours > 0 else f"{elapsed_minutes}m {elapsed_seconds}s"

            lines.append(f"\n**Overall**: {completed_all}/{total_all} ({progress_pct:.1f}%) | Elapsed: {elapsed_str}")

            return "\n".join(lines)

# ============================================================================
# LLM VALIDATION
# ============================================================================

def validate_all_llms(llm_list):
    """
    Validate that all LLMs in the list are working.

    Args:
        llm_list: List of LLM names to validate

    Raises:
        RuntimeError: If any LLM fails validation
    """
    print("Validating LLMs before starting benchmarks...")
    failed_llms = []

    for llm_name in llm_list:
        print(f"  Testing {llm_name}...", end=" ", flush=True)
        if validate_llm(llm_name):
            print("✓")
        else:
            print("✗ FAILED")
            failed_llms.append(llm_name)

    if failed_llms:
        error_msg = f"The following LLMs failed validation: {', '.join(failed_llms)}"
        print(f"\n❌ Error: {error_msg}")
        send_msg(f"❌ **Validation Failed**\n{error_msg}")
        raise RuntimeError(error_msg)

    print("✓ All LLMs validated successfully\n")

# ============================================================================
# TASK EXECUTION
# ============================================================================

async def run_single_experiment(
    task_id: str,
    llm_name: str,
    dataset: str,
    run_idx: int,
    tracker: ProgressTracker,
    semaphore: asyncio.Semaphore,
    rate_limiters: Dict[str, RateLimiter]
):
    """Run a single experiment (one LLM, one dataset, one run)"""

    # Acquire global semaphore for max parallel processes
    async with semaphore:
        # Wait for rate limiter before starting
        await rate_limiters[llm_name].acquire()

        # Get the event loop for the callback
        loop = asyncio.get_event_loop()

        # Progress callback - schedule async update from sync context
        def progress_callback(event_data):
            # Use asyncio.run_coroutine_threadsafe to safely schedule from executor thread
            asyncio.run_coroutine_threadsafe(
                tracker.update_task(task_id, event_data),
                loop
            )

        # Run experiment in executor (blocking operation)
        result = await loop.run_in_executor(
            None,
            run_experiment,
            llm_name,
            MAX_RETRY,
            1,  # num_runs = 1 (we handle multiple runs ourselves)
            run_idx,
            [dataset],  # Single dataset
            progress_callback
        )

        return result

async def run_all_benchmarks():
    """Run all benchmarks with smart distribution"""

    tracker = ProgressTracker()

    # Create global semaphore for max parallel processes
    global_semaphore = asyncio.Semaphore(MAX_PARALLEL_PROCESSES)

    # Create rate limiters for each LLM
    rate_limiters = {}
    for llm_name in LLM_LIST:
        rate_limit = LLM_RATE_LIMITS.get(llm_name, 500)  # Default to 500 if not specified
        rate_limiters[llm_name] = RateLimiter(rate_limit)

    # Generate all tasks (llm, dataset, run_idx combinations)
    # Ordered by dataset speed (slowest first)
    tasks = []
    task_id = 0

    for dataset in DATASET_ORDER_BY_SPEED:
        if dataset not in TARGET_DATASETS:
            continue
        for run_idx in range(START_RUN, START_RUN + NUM_RUN):
            for llm_name in LLM_LIST:
                task_id_str = f"task_{task_id}"
                tasks.append((task_id_str, llm_name, dataset, run_idx))
                await tracker.register_task(task_id_str, llm_name, dataset, run_idx)
                task_id += 1

    # Send initial message
    rate_limit_info = '\n'.join([f"  - {llm}: {LLM_RATE_LIMITS.get(llm, 500)}/min" for llm in LLM_LIST])
    send_msg("🚀 **Starting Async LLM Benchmarks**\n"
             f"- LLMs: {len(LLM_LIST)}\n"
             f"- Datasets: {len([d for d in DATASET_ORDER_BY_SPEED if d in TARGET_DATASETS])}\n"
             f"- Runs per dataset: {NUM_RUN}\n"
             f"- Total tasks: {len(tasks)}\n"
             f"- Max parallel: {MAX_PARALLEL_PROCESSES}\n"
             f"- Rate limits:\n{rate_limit_info}")

    # Create coroutines for all tasks
    coroutines = [
        run_single_experiment(
            task_id_str,
            llm_name,
            dataset,
            run_idx,
            tracker,
            global_semaphore,
            rate_limiters
        )
        for task_id_str, llm_name, dataset, run_idx in tasks
    ]

    # Progress reporting task
    async def report_progress():
        """Periodically report progress to Discord"""
        while True:
            await asyncio.sleep(600)  # Report every 10 minutes
            report = await tracker.get_progress_report()
            send_msg(report)

    # Start progress reporting
    progress_task = asyncio.create_task(report_progress())

    # Run all experiments
    try:
        results = await asyncio.gather(*coroutines, return_exceptions=True)

        # Check for errors
        errors = [r for r in results if isinstance(r, Exception)]
        if errors:
            send_msg(f"⚠️ **Completed with {len(errors)} errors**")
            for error in errors[:5]:  # Show first 5 errors
                send_msg(f"Error: {str(error)[:500]}")

        # Final report
        final_report = await tracker.get_progress_report()
        send_msg(f"✅ **All Benchmarks Complete!**\n\n{final_report}")

    finally:
        progress_task.cancel()
        try:
            await progress_task
        except asyncio.CancelledError:
            pass

# ============================================================================
# MAIN
# ============================================================================

def main():
    """Main entry point"""
    if not os.path.exists("dataset"):
        print("Error: 'dataset' folder not found.")
        return

    # Validate all LLMs before starting
    try:
        validate_all_llms(LLM_LIST)
    except RuntimeError as e:
        print(f"\nExiting due to LLM validation failure.")
        sys.exit(1)

    # Run async event loop
    asyncio.run(run_all_benchmarks())

if __name__ == "__main__":
    main()
