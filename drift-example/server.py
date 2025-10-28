from fastapi import FastAPI
from fastapi.responses import HTMLResponse, JSONResponse
import uvicorn

app = FastAPI()

@app.get("/todos/json_mismatch/{id}")
def json_mismatch(id: int):
    if id == 1:
        return {"id": 1, "title": "Learn Agda"}      
    else:
        return {"id": 2, "name": "Learn Python"}   

@app.get("/todos/status_mismatch/{id}")
def status_mismatch(id: int):
    if id == 1:
        return {"id": 1, "title": "Learn Agda"} 
    else:
        return JSONResponse(content={"error": "Not found"}, status_code=200)

@app.get("/todos/content_mismatch/{id}", response_class=HTMLResponse)
def content_mismatch(id: int):
    return "<h1>Oops, not JSON</h1>"

if __name__ == "__main__":
    uvicorn.run(app, host="127.0.0.1", port=8000)
