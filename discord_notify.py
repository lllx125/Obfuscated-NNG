"""
Discord Webhook Progress Notification System
Sends progress updates and crash reports to Discord during long-running jobs.
"""

import os
import requests
import traceback


WEBHOOK_URL = "https://discord.com/api/webhooks/1450642863212855336/wN-tvEiSHOJ1Yn-Yc9dSWQYdHnZc_cLyHjSC39ezufLYwDZGTakYCj6xcqYJQK9Nc8UA"

TAG = os.getenv("TAG", "local")
LLM_NAME = os.getenv("LLM_NAME", "unknown")


def build_progress_message(message, run_info=None, time_info=None):
    """Builds a progress message with run info and time estimation

    Args:
        message: The main message
        run_info: Optional dict with 'current_run' and 'total_runs'
        time_info: Optional dict with 'elapsed_time', 'completed_queries', 'total_queries'

    Returns:
        Formatted message string with progress info
    """
    full_message = f'{message}\n🔖 Model: `{LLM_NAME}`'

    if run_info:
        full_message += f'\n📍 Run: {run_info["current_run"]}/{run_info["total_runs"]}'

    if time_info:
        elapsed = time_info['elapsed_time']
        completed = time_info['completed_queries']
        total = time_info['total_queries']

        # Calculate estimated time left
        if completed > 0:
            avg_time_per_query = elapsed / completed
            remaining_queries = total - completed
            estimated_time_left = avg_time_per_query * remaining_queries

            # Format time remaining
            hours, remainder = divmod(int(estimated_time_left), 3600)
            minutes, seconds = divmod(remainder, 60)

            time_str = ""
            if hours > 0:
                time_str += f"{hours}h "
            if minutes > 0:
                time_str += f"{minutes}m "
            time_str += f"{seconds}s"

            progress_pct = (completed / total) * 100
            full_message += f'\n⏱️ Progress: {completed}/{total} queries ({progress_pct:.1f}%) | ETA: {time_str}'

    return full_message


def send_msg(message):
    """Sends a message to Discord"""
    # Only send if remote mode is enabled
    if TAG == "local":
        return

    if not WEBHOOK_URL.startswith("http"):
        print("Error: Webhook URL not set.")
        return

    data = {"content": f'**{TAG}**: {message}'}
    try:
        requests.post(WEBHOOK_URL, json=data)
    except Exception as e:
        print(f"Failed to send Discord message: {e}")


class DiscordProgress:
    """Context Manager to handle crashes automatically"""

    def __enter__(self):
        send_msg("🚀 **Job Started**: LLM Inference has begun.")
        return self

    def __exit__(self, exc_type, exc_value, exc_traceback):
        if exc_type:
            # If an error occurred, format it and send it
            error_message = "".join(traceback.format_exception(exc_type, exc_value, exc_traceback))
            # Discord limits messages to 2000 chars, so we truncate if needed
            send_msg(f"🚨 **CRASH DETECTED** 🚨\n```python\n{error_message[:1900]}\n```")
        else:
            send_msg("✅ **Job Finished**: The run is complete.")

        # Don't suppress exceptions - let them propagate
        return False
