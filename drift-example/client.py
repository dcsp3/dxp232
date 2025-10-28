import requests
import json

def test_client(endpoint):
    print()
    print("============================================================")
    print(f"Testing endpoint: {endpoint}")
    print("============================================================")

    try:
        res = requests.get(f"http://127.0.0.1:8000{endpoint}")
        print("Request successful.")
    except requests.RequestException as e:
        print(f"Network error ({type(e).__name__}): {e}")
        print()
        return

    print("Status code:", res.status_code)
    print()

    try:
        todo = res.json()
        print(f"Parsed JSON:\n {json.dumps(todo, indent=4)}")
    except Exception as e:
        print(f"Error parsing JSON ({type(e).__name__}): {e}")
        print()
        return

    print()
    try:
        title = todo["title"]
        print(f"Accessing title: {title}")
        print(f"Uppercase title: {title.upper()}")
    except Exception as e:
        print(f"Error accessing or processing title ({type(e).__name__}): {e}")

if __name__ == "__main__":
    test_client("/todos/json_mismatch/4")
    test_client("/todos/status_mismatch/266")
    test_client("/todos/content_mismatch/1")
