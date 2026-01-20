Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["233/522"; "23/522"] -> x1=233, x2=522, n1=23, n2=522
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 233 522 23 522 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (233 * 23) mod (522 * 522) *)
    (* 233 * 23 = 5359 *)
    (* 522 * 522 = 272484 *)
    (* 5359 mod 272484 = 5359 *)
    (* H_mod becomes 5359 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.