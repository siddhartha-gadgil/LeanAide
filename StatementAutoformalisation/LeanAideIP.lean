/-- The IP address of the `LeanAide` server hosting the Python code. -/
def leanAideIP : IO String := do
  -- the current IP address of the server is: `34.100.184.111:5000` 
  let some ip ← IO.getEnv "LEANAIDE_IP" | do 
    IO.println "Defaulting to local IP ..."
    pure "localhost:5000"
  return ip