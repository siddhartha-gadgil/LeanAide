import LeanAide.JsonDiff
import Lean
open Lean.Json
open LeanAide JsonDiff
-- Both objects are empty
def j_empty_obj_1a := json% {}
def j_empty_obj_1b := json% {}
/-- info: [] -/
#guard_msgs in
#eval jsonDiff j_empty_obj_1a j_empty_obj_1b
-- One object is empty, the other is not
def j_empty_obj_2a := json% {}
def j_empty_obj_2b := json% {"a": 1}
/-- info: [LeanAide.JsonDiff.existsKey2only "a" "1"] -/
#guard_msgs in
#eval jsonDiff j_empty_obj_2a j_empty_obj_2b
-- Both arrays are empty
def j_empty_arr_1a := json% []
def j_empty_arr_1b := json% []
/-- info: [] -/
#guard_msgs in
#eval jsonDiff j_empty_arr_1a j_empty_arr_1b
-- One array is empty, the other is not
def j_empty_arr_2a := json% []
def j_empty_arr_2b := json% [1, 2]
/--
info: [LeanAide.JsonDiff.atIndex 0 (LeanAide.JsonDiff.message "first list does not have element"),
 LeanAide.JsonDiff.atIndex 1 (LeanAide.JsonDiff.message "first list does not have element")]
-/
#guard_msgs in
#eval jsonDiff j_empty_arr_2a j_empty_arr_2b
-- Comparing an empty object and an empty array
def j_empty_mix_a := json% {}
def j_empty_mix_b := json% []
/-- info: [LeanAide.JsonDiff.message "terms have different types: {} versus []"] -/
#guard_msgs in
#eval jsonDiff j_empty_mix_a j_empty_mix_b
-- Comparing two null values
def j_null_1a := null
def j_null_1b := null
/-- info: [] -/
#guard_msgs in
#eval jsonDiff j_null_1a j_null_1b
-- Comparing null with a non-null value
def j_null_2a := null
def j_null_2b := json% {"a": null}
/-- info: [LeanAide.JsonDiff.message "terms have different types: null versus {\"a\":null}"] -/
#guard_msgs in
#eval jsonDiff j_null_2a j_null_2b

-- Key exists in the first object only
def j_key_first_only_a := json% {"a": 1, "b": 2}
def j_key_first_only_b := json% {"a": 1}
/-- info: [LeanAide.JsonDiff.existsKey1only "b" "2"] -/
#guard_msgs in
#eval jsonDiff j_key_first_only_a j_key_first_only_b
-- Key exists in the second object only
def j_key_second_only_a := json% {"a": 1}
def j_key_second_only_b := json% {"a": 1, "c": 3}
/-- info: [LeanAide.JsonDiff.existsKey2only "c" "3"] -/
#guard_msgs in
#eval jsonDiff j_key_second_only_a j_key_second_only_b
-- Different key casing (treated as different keys)
def j_key_casing_a := json% {"key": "value"}
def j_key_casing_b := json% {"Key": "value"}
/--
info: [LeanAide.JsonDiff.existsKey1only "key" "\"value\"", LeanAide.JsonDiff.existsKey2only "Key" "\"value\""]
-/
#guard_msgs in
#eval jsonDiff j_key_casing_a j_key_casing_b
-- Keys are a mix of present in one, both, or the other
def j_key_mix_a := json% {"common": 1, "only_a": 2}
def j_key_mix_b := json% {"common": 1, "only_b": 3}
/--
info: [LeanAide.JsonDiff.existsKey1only "only_a" "2", LeanAide.JsonDiff.existsKey2only "only_b" "3"]
-/
#guard_msgs in
#eval jsonDiff j_key_mix_a j_key_mix_b

-- Different string values
def j_val_str_a := json% {"status": "active"}
def j_val_str_b := json% {"status": "inactive"}
/--
info: [LeanAide.JsonDiff.atKey "status" (LeanAide.JsonDiff.message "one has string active and another has string inactive")]
-/
#guard_msgs in
#eval jsonDiff j_val_str_a j_val_str_b
-- Different number values (integer vs float)
def j_val_num_a := json% {"score": 100}
def j_val_num_b := json% {"score": 99.5}
/--
info: [LeanAide.JsonDiff.atKey "score" (LeanAide.JsonDiff.message "one has number 100 and another has number 99.5")]
-/
#guard_msgs in
#eval jsonDiff j_val_num_a j_val_num_b
-- Different boolean values
def j_val_bool_a := json% {"isEnabled": true}
def j_val_bool_b := json% {"isEnabled": false}
/--
info: [LeanAide.JsonDiff.atKey "isEnabled" (LeanAide.JsonDiff.message "one has boolean true and another has boolean false")]
-/
#guard_msgs in
#eval jsonDiff j_val_bool_a j_val_bool_b
-- Same numeric value, but different JSON types (number vs string)
def j_val_type_a := json% {"id": 123}
def j_val_type_b := json% {"id": "123"}
/--
info: [LeanAide.JsonDiff.atKey "id" (LeanAide.JsonDiff.message "terms have different types: 123 versus \"123\"")]
-/
#guard_msgs in
#eval jsonDiff j_val_type_a j_val_type_b
-- Arrays of different lengths (first is shorter)
def j_arr_len_1a := json% [1, 2]
def j_arr_len_1b := json% [1, 2, 3]
/-- info: [LeanAide.JsonDiff.atIndex 2 (LeanAide.JsonDiff.message "first list does not have element")] -/
#guard_msgs in
#eval jsonDiff j_arr_len_1a j_arr_len_1b
-- Arrays of different lengths (first is longer)
def j_arr_len_2a := json% ["a", "b", "c"]
def j_arr_len_2b := json% ["a", "b"]
/-- info: [LeanAide.JsonDiff.atIndex 2 (LeanAide.JsonDiff.message "second list does not have element")] -/
#guard_msgs in
#eval jsonDiff j_arr_len_2a j_arr_len_2b
-- Same length, different elements
def j_arr_elem_a := json% [1, 2, 3]
def j_arr_elem_b := json% [1, 5, 3]
/--
info: [LeanAide.JsonDiff.atIndex 1 (LeanAide.JsonDiff.message "one has number 2 and another has number 5")]
-/
#guard_msgs in
#eval jsonDiff j_arr_elem_a j_arr_elem_b
-- Same length, different element types at an index
def j_arr_type_a := json% [1, "ok", 3]
def j_arr_type_b := json% [1, true, 3]
/--
info: [LeanAide.JsonDiff.atIndex 1 (LeanAide.JsonDiff.message "terms have different types: \"ok\" versus true")]
-/
#guard_msgs in
#eval jsonDiff j_arr_type_a j_arr_type_b
-- Difference inside a nested object
def j_nested_obj_a := json% {"config": {"retries": 3, "delay": 100}}
def j_nested_obj_b := json% {"config": {"retries": 5, "delay": 100}}
/--
info: [LeanAide.JsonDiff.atKey
   "config"
   (LeanAide.JsonDiff.atKey "retries" (LeanAide.JsonDiff.message "one has number 3 and another has number 5"))]
-/
#guard_msgs in
#eval jsonDiff j_nested_obj_a j_nested_obj_b
-- A key is an object in one and a primitive in another
def j_nested_type_a := json% {"user": {"name": "Alex"}}
def j_nested_type_b := json% {"user": "Alex"}
/--
info: [LeanAide.JsonDiff.atKey
   "user"
   (LeanAide.JsonDiff.message "terms have different types: {\"name\":\"Alex\"} versus \"Alex\"")]
-/
#guard_msgs in
#eval jsonDiff j_nested_type_a j_nested_type_b
-- Difference inside an array within an object
def j_nested_arr_a := json% {"items": [1, 2, 3]}
def j_nested_arr_b := json% {"items": [1, 9, 3]}
/--
info: [LeanAide.JsonDiff.atKey
   "items"
   (LeanAide.JsonDiff.atIndex 1 (LeanAide.JsonDiff.message "one has number 2 and another has number 9"))]
-/
#guard_msgs in
#eval jsonDiff j_nested_arr_a j_nested_arr_b
-- Difference inside an object within an array
def j_arr_nested_obj_a := json% [{"id": 1, "val": "x"}, {"id": 2, "val": "y"}]
def j_arr_nested_obj_b := json% [{"id": 1, "val": "x"}, {"id": 2, "val": "z"}]
/--
info: [LeanAide.JsonDiff.atIndex
   1
   (LeanAide.JsonDiff.atKey "val" (LeanAide.JsonDiff.message "one has string y and another has string z"))]
-/
#guard_msgs in
#eval jsonDiff j_arr_nested_obj_a j_arr_nested_obj_b
-- A very complex, deeply nested difference
def j_complex_a := json% {
  "id": "abc-123",
  "metadata": {
    "timestamp": "2025-10-18T14:30:00Z",
    "tags": ["prod", "api"]
  },
  "payload": [
    {"sensor": "temp", "reading": 23.5},
    {"sensor": "humidity", "reading": 45}
  ]
}
def j_complex_b := json% {
  "id": "abc-123",
  "metadata": {
    "timestamp": "2025-10-18T14:35:00Z",
    "tags": ["prod", "web"]
  },
  "payload": [
    {"sensor": "temp", "reading": 23.5},
    {"sensor": "humidity", "reading": 48, "unit": "%"}
  ]
}
/--
info: [LeanAide.JsonDiff.atKey
   "metadata"
   (LeanAide.JsonDiff.atKey
     "tags"
     (LeanAide.JsonDiff.atIndex 1 (LeanAide.JsonDiff.message "one has string api and another has string web"))),
 LeanAide.JsonDiff.atKey
   "metadata"
   (LeanAide.JsonDiff.atKey
     "timestamp"
     (LeanAide.JsonDiff.message "one has string 2025-10-18T14:30:00Z and another has string 2025-10-18T14:35:00Z")),
 LeanAide.JsonDiff.atKey
   "payload"
   (LeanAide.JsonDiff.atIndex
     1
     (LeanAide.JsonDiff.atKey "reading" (LeanAide.JsonDiff.message "one has number 45 and another has number 48"))),
 LeanAide.JsonDiff.atKey "payload" (LeanAide.JsonDiff.atIndex 1 (LeanAide.JsonDiff.existsKey2only "unit" "\"%\""))]
-/
#guard_msgs in
#eval jsonDiff j_complex_a j_complex_b
