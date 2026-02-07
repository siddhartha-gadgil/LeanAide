import Mathlib
import LeanAide
open Nat LeanAide
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u v u_1

namespace LeanAide.DetSkewSymm

def detOfSkew := json% {
  "document": {
    "type": "document",
    "body": [
      {
        "type": "Theorem",
        "label": "thm:skew_det_odd",
        "header": "Theorem",
        "hypothesis": [
          {
            "type": "let_statement",
            "variable_name": "n",
            "variable_type": "ℕ",
            "statement": "Let n : ℕ."
          },
          {
            "type": "assume_statement",
            "label": "h_odd",
            "assumption": "n is odd"
          },
          {
            "type": "let_statement",
            "variable_name": "A",
            "variable_type": "Matrix(Fin n, Fin n, ℝ)",
            "statement": "Let A : Matrix(Fin n, Fin n, ℝ)."
          },
          {
            "type": "assume_statement",
            "label": "h_skew",
            "assumption": "A^T = -A"
          }
        ],
        "claim": "det(A) = 0",
        "proof": [
          {
            "type": "Theorem",
            "label": "lem:det_transpose",
            "header": "Lemma",
            "claim": "For any M: Matrix(Fin n, Fin n, ℝ), det(M^T) = det(M).",
            "proof": [
              {
                "type": "assert_statement",
                "claim": "Swapping rows and columns in the determinant sum does not change any term, hence det(M^T) = det(M)."
              }
            ]
          },
          {
            "type": "Theorem",
            "label": "lem:det_scaling",
            "header": "Lemma",
            "claim": "For any c: ℝ and M: Matrix(Fin n, Fin n, ℝ), det(c·M) = c^n det(M).",
            "proof": [
              {
                "type": "assert_statement",
                "claim": "Determinant is multilinear in its rows, so scaling each of the n rows by c multiplies the determinant by c^n."
              }
            ]
          },
          {
            "type": "assert_statement",
            "label": "h_1",
            "claim": "det(A) = det(A^T)",
            "results_used": [
              {
                "statement": "det(M^T) = det(M)",
                "target_identifier": "lem:det_transpose"
              }
            ]
          },
          {
            "type": "assert_statement",
            "label": "h_2",
            "claim": "det(A^T) = det(-A)",
            "proof_method": "Using A^T = -A"
          },
          {
            "type": "assert_statement",
            "label": "h_3",
            "claim": "det(-A) = (-1)^n det(A)",
            "results_used": [
              {
                "statement": "det(c·M) = c^n det(M)",
                "target_identifier": "lem:det_scaling"
              }
            ]
          },
          {
            "type": "assert_statement",
            "label": "h_4",
            "claim": "(-1)^n = -1",
            "proof_method": "Since n is odd, write n = 2k+1 and compute (-1)^{2k+1} = -1"
          },
          {
            "type": "assert_statement",
            "claim": "det(A) = - det(A)",
            "results_used": [
              {
                "statement": "det(A) = det(A^T)",
                "target_identifier": "h_1"
              },
              {
                "statement": "det(A^T) = det(-A)",
                "target_identifier": "h_2"
              },
              {
                "statement": "det(-A) = (-1)^n det(A)",
                "target_identifier": "h_3"
              },
              {
                "statement": "(-1)^n = -1",
                "target_identifier": "h_4"
              }
            ]
          },
          {
            "type": "assert_statement",
            "claim": "2 det(A) = 0",
            "proof_method": "Rearranging det(A) = - det(A)"
          },
          {
            "type": "assert_statement",
            "claim": "det(A) = 0",
            "proof_method": "Multiplying both sides of 2 det(A) = 0 by 2^{-1} in ℝ"
          }
        ]
      }
    ]
  }
}
