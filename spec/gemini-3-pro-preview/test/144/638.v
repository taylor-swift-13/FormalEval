Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/5271"; "921/739"] -> x1=23, x2=5271, n1=921, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 5271 921 739 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (23 * 921) mod (5271 * 739) *)
    (* 23 * 921 = 21183 *)
    (* 5271 * 739 = 3895269 *)
    (* 21183 mod 3895269 = 21183 *)
    (* H_mod states 21183 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.