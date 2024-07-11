import LeanCodePrompts.ChatClient
open Lean

#eval proofExample

def gemini := ChatServer.google

def structExampl := gemini.structuredProof proofExample

-- #eval structExampl
