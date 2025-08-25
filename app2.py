from fasthtml.common import *

app, rt = fast_app()

# Counters for each tab
counter1 = 0
counter2 = 0

@app.get("/tab1")
def get_tab1_content():
    global counter1
    return Div(
        H2("Counter 1"),
        P(f"Current count: {counter1}", id="counter1-display"),
        Button("Increment Counter 1", hx_post="/increment1", hx_target="#counter1-display", hx_swap="innerHTML"),
    )

@app.get("/tab2")
def get_tab2_content():
    global counter2
    return Div(
        H2("Counter 2"),
        P(f"Current count: {counter2}", id="counter2-display"),
        Button("Increment Counter 2", hx_post="/increment2", hx_target="#counter2-display", hx_swap="innerHTML"),
    )

@app.post("/increment1")
def increment_counter1():
    global counter1
    counter1 += 1
    return f"Current count: {counter1}"

@app.post("/increment2")
def increment_counter2():
    global counter2
    counter2 += 1
    return f"Current count: {counter2}"

@app.get("/")
def home():
    return Title("Tabbed Counters"), Div(
        Nav(
            Ul(
                Li(A("Tab 1", href="#", hx_get="/tab1", hx_target="#tab-content", hx_swap="innerHTML")),
                Li(A("Tab 2", href="#", hx_get="/tab2", hx_target="#tab-content", hx_swap="innerHTML")),
            ),
        ),
        Div(id="tab-content", hx_get="/tab1", hx_trigger="load", hx_swap="innerHTML"),
        style="margin: 1em;"# Initial load of Tab 1
    )

if __name__ == "__main__":
    serve()
