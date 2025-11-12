
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition simplify_spec (x n : string) (result : bool) : Prop :=
  let (x1, x2) := match split_string x "/" with
                  | [x1_str; x2_str] => (int_of_string x1_str, int_of_string x2_str)
                  | _ => (0, 0) (* Invalid case, should not happen *)
                  end in
  let (n1, n2) := match split_string n "/" with
                  | [n1_str; n2_str] => (int_of_string n1_str, int_of_string n2_str)
                  | _ => (0, 0) (* Invalid case, should not happen *)
                  end in
  result = ((x1 * n1) mod (x2 * n2) =? 0).
