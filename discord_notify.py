"""
Discord Webhook Progress Notification System
Sends progress updates and crash reports to Discord during long-running jobs.
"""

import os
import requests
import traceback


WEBHOOK_URL = "https://discord.com/api/webhooks/1450642863212855336/wN-tvEiSHOJ1Yn-Yc9dSWQYdHnZc_cLyHjSC39ezufLYwDZGTakYCj6xcqYJQK9Nc8UA"

DEVICE_NAME = os.getenv("DEVICE_NAME", "local")


def send_msg(message):
    """Sends a message to Discord"""
    # Only send if remote mode is enabled
    if DEVICE_NAME == "local":
        return

    if not WEBHOOK_URL.startswith("http"):
        print("Error: Webhook URL not set.")
        return

    data = {"content": f'**{DEVICE_NAME}**: {message}'}
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
