Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/99"; "921/739"] -> x1=111, x2=99, n1=921, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 111 99 921 739 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* We need to show that mod = 0 implies false = true (contradiction).
       Calculate (111 * 921) mod (99 * 739).
       111 * 921 = 102231
       99 * 739 = 73161
       102231 mod 73161 = 29070 <> 0
    *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.