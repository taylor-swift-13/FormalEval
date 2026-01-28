Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163/58"; "921/73"] -> x1=163, x2=58, n1=921, n2=73
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 163 58 921 73 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the values: (163 * 921) mod (58 * 73) *)
    (* 163 * 921 = 150123 *)
    (* 58 * 73 = 4234 *)
    (* 150123 mod 4234 = 1933 *)
    (* H_mod becomes 1933 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.