from fastapi import FastAPI
from pydantic import BaseModel


def calculate(operation, x, y):
    '''
    operation - takes the string [add, sub, mul, div]
    x & y - two numbers
    ''' 
    if operation == 'Addition':
        return x+y
    
    elif operation == 'Subtraction':
        if x>y:
            return x-y
        else:
            return y-x

    elif operation == 'Multiplication':
        return x*y
    
    elif operation == 'Division':
        return x/y

class User_input(BaseModel):
    operation : str
    x : float
    y : float

app = FastAPI()

@app.post("/")
def operate(input:User_input):
    result = calculate(input.operation, input.x, input.y)
    return result
