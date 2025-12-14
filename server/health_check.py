"""
LeanAide Server Health Checker

This script performs comprehensive health checks on the LeanAide server:
1. Socket connectivity test - checks if port is open and accepting connections
2. HTTP endpoint test - sends a test request to verify server is responding
3. Auto-restart - if server is down, attempts to start it in the background

Usage:
    python health_check.py [--start-if-down] [--verbose]
"""

import argparse
import json
import os
import socket
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path

LEANAIDE_ADDR = os.getenv("LEANAIDE_ADDR", "10.134.13.103")
LEANAIDE_PORT = os.getenv("LEANAIDE_PORT", "7654")
LEANAIDE_ROOT = Path(__file__).parent.parent
SERVER_ARGS = "--ui"
SERVER_SCRIPT = LEANAIDE_ROOT / "leanaide_server.py"
PYTHON_ENV = "/home/anirudhgupta/LeanAide/server/.venv/bin/python3"
LEANAIDE_LOG_FILE = "/home/anirudhgupta/.leanaide/server_health.log"
TIMEOUT_SECONDS = 300  # 5 minutes - server might be processing a request
TMUX_SESSION_NAME = "leanaide-server"

def println(message: str, verbose: bool):
    """Print message if verbose is enabled"""
    if verbose:
        print(message)


def kill_leanaide_processes(verbose=False):
    """
    Kill all LeanAide-related processes (leanaide_server.py and leanaide_process).
    Only kills processes owned by the current user.
    
    Returns:
        int: Number of processes killed
    """
    println("Searching for LeanAide processes to kill...", verbose)
    
    try:
        # Get all processes related to leanaide
        result = subprocess.run(
            ["ps", "aux"],
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result.returncode != 0:
            println("✗ Failed to list processes", verbose)
            return 0
        
        # Filter for leanaide processes
        killed_count = 0
        current_user = subprocess.run(
            ["whoami"],
            capture_output=True,
            text=True
        ).stdout.strip()
        
        for line in result.stdout.splitlines():
            # Look for leanaide_server.py or leanaide_process
            if ("leanaide_server.py" in line or "leanaide_process" in line) and current_user in line:
                parts = line.split()
                if len(parts) >= 2:
                    pid = parts[1]
                    try:
                        # Kill the process
                        subprocess.run(["kill", "-9", pid], check=True, timeout=5)
                        println(f"✓ Killed process {pid}: {' '.join(parts[10:])}", verbose)
                        killed_count += 1
                    except subprocess.CalledProcessError:
                        println(f"✗ Failed to kill process {pid}", verbose)
                    except subprocess.TimeoutExpired:
                        println(f"✗ Timeout killing process {pid}", verbose)
        
        if killed_count > 0:
            println(f"✓ Killed {killed_count} LeanAide process(es)", verbose)
            # Give processes time to terminate
            time.sleep(2)
        else:
            println("No LeanAide processes found to kill", verbose)
        
        return killed_count
        
    except Exception as e:
        println(f"✗ Error killing processes: {e}", verbose)
        return 0


def tmux_session_exists(session_name):
    """Check if a tmux session exists"""
    try:
        result = subprocess.run(
            ["tmux", "has-session", "-t", session_name],
            capture_output=True,
            timeout=5
        )
        return result.returncode == 0
    except Exception:
        return False


def start_server_in_tmux(verbose=False, kill_first=False):
    """
    Start the LeanAide server in a tmux session for easy monitoring.
    
    Returns:
        bool: True if server started successfully, False otherwise
    """
    if not SERVER_SCRIPT.exists():
        println(f"✗ Server script not found at {SERVER_SCRIPT}", verbose)
        return False

    println(f"Starting LeanAide server in tmux session '{TMUX_SESSION_NAME}'...", verbose)

    try:
        # Get the Python executable
        python_cmd = PYTHON_ENV if Path(PYTHON_ENV).exists() else "python3"
        
        # If a tmux session already exists, don't kill the session.
        # Optionally kill only the LeanAide processes (not the tmux session),
        # then start the server in a new window under the existing session.
        if tmux_session_exists(TMUX_SESSION_NAME):
            println(f"Found existing tmux session '{TMUX_SESSION_NAME}' - leaving session intact", verbose)

            if kill_first:
                killed = kill_leanaide_processes(verbose)
                println(f"Killed {killed} LeanAide process(es) (session preserved)", verbose)

                # Create a new window in the existing session to run the server.
                # kill the tmux session.
                cmd = f"echo Starting server; exec {python_cmd} {str(SERVER_SCRIPT)} {SERVER_ARGS}"
                tmux_cmd = [
                    "tmux", "new-window", "-t", TMUX_SESSION_NAME,
                    "-n", "leanaide", "-c", str(LEANAIDE_ROOT),
                    "bash", "-lc", cmd,
                ]
        else:
            # Create new tmux session and start server
            # -d: detached mode (don't attach immediately)
            # -s: session name
            cmd = f"echo Starting server; exec {python_cmd} {str(SERVER_SCRIPT)} {SERVER_ARGS}"
            tmux_cmd = [
                "tmux", "new-session", "-d", "-s", TMUX_SESSION_NAME,
                "-c", str(LEANAIDE_ROOT),  # Change to LeanAide directory
                "bash", "-lc", cmd,
            ]
        
        result = subprocess.run(
            tmux_cmd,
            capture_output=True,
            text=True,
            timeout=10
        )
        
        if result.returncode != 0:
            println(f"✗ Failed to create tmux session: {result.stderr}", verbose)
            return False

        wait_time = 10
        
        println(f"✓ Server started in tmux session '{TMUX_SESSION_NAME}'", verbose)
        println(f"  To attach: tmux attach -t {TMUX_SESSION_NAME}", verbose)
        println("  To detach: Ctrl+B, then D", verbose)
        println(f"  Waiting {wait_time} seconds for server to initialize...", verbose)

        # Give server time to start
        time.sleep(wait_time)

        # Verify it's actually running
        if test_socket(verbose=False):
            println("✓ Server is now responding", verbose)
            return True
        else:
            println("⚠ Server started but not yet responding (may need more time)", verbose)
            return False
            
    except Exception as e:
        println(f"✗ Failed to start server in tmux: {e}", verbose)
        return False


def test_socket(verbose=False):
    """
    Test if the server port is open and accepting connections.
    
    Returns:
        bool: True if server is reachable, False otherwise
    """
    println(f"Testing socket connection to {LEANAIDE_ADDR}:{LEANAIDE_PORT}...", verbose)

    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(TIMEOUT_SECONDS)
        result = sock.connect_ex((LEANAIDE_ADDR, LEANAIDE_PORT))
        sock.close()
        
        if result == 0:
            println("✓ Socket connection successful", verbose)
            return True
        else:
            println(f"✗ Socket connection failed with code {result}", verbose)
            return False
            
    except socket.timeout:
        println(f"✗ Socket connection timed out after {TIMEOUT_SECONDS} seconds", verbose)
        return False
    except Exception as e:
        println(f"✗ Socket connection error: {e}", verbose)
        return False


def test_http_endpoint(verbose=False):
    """
    Send a test HTTP request to verify server is responding correctly.
    Uses a minimal request to the root endpoint.
    
    Returns:
        bool: True if server responds correctly, False otherwise
    """
    println(f"Testing HTTP endpoint at http://{LEANAIDE_ADDR}:{LEANAIDE_PORT}...", verbose)

    try:
        url = f"http://{LEANAIDE_ADDR}:{LEANAIDE_PORT}/"
        req = urllib.request.Request(url, method='GET')
        
        with urllib.request.urlopen(req, timeout=TIMEOUT_SECONDS) as response:
            status = response.status
            println(f"✓ HTTP endpoint responded with status {status}", verbose)
            return status in [200, 404]  # 404 is OK if no root handler
            
    except urllib.error.URLError as e:
        println(f"✗ HTTP endpoint error: {e}", verbose)
        return False
    except Exception as e:
        println(f"✗ Unexpected error testing HTTP endpoint: {e}", verbose)
        return False


def start_server(verbose=False, use_tmux=True, kill_first=False):
    """
    Start the LeanAide server.
    
    Args:
        verbose: Print detailed status messages
        use_tmux: Start in tmux session (recommended for monitoring)
    
    Returns:
        bool: True if server started successfully, False otherwise
    """
    if use_tmux:
        return start_server_in_tmux(verbose, kill_first=kill_first)
    
    # Fallback: Start without tmux
    if not SERVER_SCRIPT.exists():
        println(f"✗ Server script not found at {SERVER_SCRIPT}", verbose)
        return False

    println(f"Starting LeanAide server from {SERVER_SCRIPT}...", verbose)

    try:
        # Get the Python executable (prefer python3)
        python_cmd = PYTHON_ENV if Path(PYTHON_ENV).exists() else "python3"
        
        # Start server in background, detached from this process
        # Redirect output to logs
        with open(LEANAIDE_LOG_FILE, 'a') as log:
            log.write(f"\n{'='*60}\n")
            log.write(f"Starting server at {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            log.write(f"{'='*60}\n")
            
            args = [python_cmd, str(SERVER_SCRIPT)]
            if SERVER_ARGS:
                args += SERVER_ARGS.split()

            process = subprocess.Popen(
                args,
                cwd=str(LEANAIDE_ROOT),
                stdout=log,
                stderr=log,
                start_new_session=True  # Detach from parent
            )

        wait_time = 10
        
        println(f"✓ Server process started with PID {process.pid}", verbose)
        println(f"  Logs: {LEANAIDE_LOG_FILE}", verbose)
        println(f"  Waiting {wait_time} seconds for server to initialize...", verbose)

        # Give server time to start
        time.sleep(wait_time)

        # Verify it's actually running
        if test_socket(verbose=False):
            println("✓ Server is now responding", verbose)
            return True
        else:
            println("⚠ Server started but not yet responding (may need more time)", verbose)
            return False
            
    except Exception as e:
        println(f"✗ Failed to start server: {e}", verbose)
        return False


def perform_health_check(start_if_down=False, kill_first=False, verbose=False):
    """
    Perform complete health check of the LeanAide server.
    
    Args:
        start_if_down: If True, attempt to start server if it's down
        kill_first: If True, kill existing LeanAide processes before starting
        verbose: If True, print detailed status messages
        
    Returns:
        dict: Health check results with status and details
    """
    results = {
        "timestamp": time.strftime('%Y-%m-%d %H:%M:%S'),
        "server": f"{LEANAIDE_ADDR}:{LEANAIDE_PORT}",
        "socket_test": False,
        "http_test": False,
        "overall_status": "down",
        "auto_restart_attempted": False,
        "auto_restart_success": False,
        "processes_killed": 0
    }
    
    # Test socket connectivity
    results["socket_test"] = test_socket(verbose)
    
    # If socket test passes, try HTTP endpoint
    if results["socket_test"]:
        results["http_test"] = test_http_endpoint(verbose)
        
        if results["http_test"]:
            results["overall_status"] = "healthy"
        else:
            results["overall_status"] = "degraded"  # Port open but not responding properly
    
    # If server is down and auto-restart is enabled
    if results["overall_status"] == "down" and start_if_down:
        println("\nServer is down. Attempting to start...", verbose)
        
        # Kill existing processes if requested
        if kill_first:
            results["processes_killed"] = kill_leanaide_processes(verbose)
        
        results["auto_restart_attempted"] = True
        results["auto_restart_success"] = start_server(verbose, use_tmux=True, kill_first=kill_first)
        
        if results["auto_restart_success"]:
            results["overall_status"] = "restarted"
    
    return results


def main():
    parser = argparse.ArgumentParser(
        description="LeanAide Server Health Checker",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        "--start-if-down",
        "-s",
        action="store_true",
        help="Automatically start the server if health check fails"
    )
    parser.add_argument(
        "--kill-first",
        "-k",
        action="store_true",
        help="Kill existing LeanAide processes before starting (requires --start-if-down)"
    )
    parser.add_argument(
        "--kill-only",
        action="store_true",
        help="Only kill existing LeanAide processes and exit"
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Print detailed status messages"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results in JSON format"
    )
    
    args = parser.parse_args()
    
    # Handle kill-only mode
    if args.kill_only:
        killed = kill_leanaide_processes(verbose=args.verbose)
        if args.json:
            print(json.dumps({"processes_killed": killed}))
        else:
            print(f"Killed {killed} LeanAide process(es)")
        sys.exit(0)
    
    # Perform health check
    results = perform_health_check(
        start_if_down=args.start_if_down,
        kill_first=args.kill_first,
        verbose=args.verbose
    )
    
    # Output results
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        status_emoji = {
            "healthy": "✓",
            "degraded": "⚠",
            "down": "✗",
            "restarted": "↻"
        }
        emoji = status_emoji.get(results["overall_status"], "?")
        print(f"{emoji} LeanAide Server Status: {results['overall_status'].upper()}")
        
        if not args.verbose:
            # Print summary
            if results["overall_status"] == "healthy":
                print(f"  Server is running at {results['server']}")
            elif results["overall_status"] == "restarted":
                print("  Server was restarted and is now running")
            elif results["overall_status"] == "degraded":
                print("  Server is accepting connections but HTTP endpoint not responding properly")
            else:
                print(f"  Server is not responding at {results['server']}")
                if not args.start_if_down:
                    print("  Use --start-if-down to automatically start the server")
    
    # Exit code based on status
    exit_codes = {
        "healthy": 0,
        "restarted": 0,
        "degraded": 1,
        "down": 2
    }
    sys.exit(exit_codes.get(results["overall_status"], 3))


if __name__ == "__main__":
    main()
