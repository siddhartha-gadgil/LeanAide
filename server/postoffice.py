# Example implementation from ChatGPT. The polling should be done by the client and the workers.
import uuid
import threading
from queue import Queue
from flask import Flask, request, jsonify, abort

app = Flask(__name__)

# Thread-safe queue for tasks
tasks_queue = Queue()
# Store results: mapping from task_id to result
results = {}
results_lock = threading.Lock()

@app.route('/submit_task', methods=['POST'])
def submit_task():
    """User submits a task. Returns a task_id."""
    data = request.get_json()
    if data is None:
        return jsonify({'error': 'Invalid JSON'}), 400
    # Generate unique task ID
    task_id = str(uuid.uuid4())
    # Put the task into the queue
    tasks_queue.put({'task_id': task_id, 'payload': data})
    # Initialize result status as pending
    with results_lock:
        results[task_id] = None
    return jsonify({'task_id': task_id}), 202

@app.route('/get_task', methods=['GET'])
def get_task():
    """Worker polls for a task. Returns one task if available, else 204."""
    try:
        task = tasks_queue.get_nowait()
    except Exception:
        # No task available
        return '', 204
    return jsonify(task), 200

@app.route('/submit_result', methods=['POST'])
def submit_result():
    """Worker submits result for a task."""
    data = request.get_json()
    if not data or 'task_id' not in data or 'result' not in data:
        return jsonify({'error': 'Must provide task_id and result in JSON'}), 400
    task_id = data['task_id']
    result = data['result']
    # Store the result
    with results_lock:
        if task_id not in results:
            return jsonify({'error': 'Unknown task_id'}), 400
        results[task_id] = result
    return jsonify({'status': 'ok'}), 200

@app.route('/get_result/<task_id>', methods=['GET'])
def get_result(task_id):
    """User polls for result of a given task_id."""
    with results_lock:
        if task_id not in results:
            return jsonify({'error': 'Unknown task_id'}), 404
        res = results[task_id]
    if res is None:
        # Still pending
        return jsonify({'status': 'pending'}), 202
    # Optionally: remove result after retrieval
    # with results_lock:
    #     del results[task_id]
    return jsonify({'status': 'done', 'result': res}), 200

if __name__ == '__main__':
    # For development only; use a production server for deployment
    app.run(host='0.0.0.0', port=5000, threaded=True)
