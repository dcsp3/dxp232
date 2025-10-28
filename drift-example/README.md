# Client-Server Drift Example

A small example demonstrating client-server drift, where a client and server disagree about an API’s expected behavior or data format.  
It illustrates how even minor inconsistencies can cause runtime errors and break compatibility.


## Overview

The example includes:
- `server.py`: a FastAPI server that intentionally returns inconsistent responses
- `client.py`: a Python client that interacts with the server and reveals drift through runtime error

### Types of Drift Demonstrated

1. **JSON Mismatch** - The server returns an unexpected field (`"name"` instead of `"title"`)
2. **Status Mismatch** - The server returns a success code (`200`) even when the resource is not found
3. **Content Mismatch** - The server returns HTML instead of JSON


## Running the Example

1. Install dependencies
    ```bash
    pip install -r requirements.txt
    ```

2. Start the server
    ```bash
    python server.py
    ```

3. Run the client (in a separate terminal)
    ```bash
    python client.py
    ```

The client will print responses and highlight where mismatches cause errors, highlighting how drift can break compatibility between systems.

---

This example shows how small mismatches between a client and server can lead to real issues in practice.  
It’s a simple demonstration of the kind of problems I aim to detect and solve with my project.