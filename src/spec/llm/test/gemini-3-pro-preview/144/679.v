Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/73"; "921/73"] -> x1=921, x2=73, n1=921, n2=73
   Output: false -> result=false
*)
Example test_simplify : simplify_spec 921 73 921 73 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_contra.
    (* false = true is impossible *)
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo: (921 * 921) mod (73 * 73) *)
    (* 848241 mod 5329 = 930 *)
    vm_compute in H_mod.
    (* H_mod becomes 930 = 0, which is impossible *)
    discriminate H_mod.
Qed.