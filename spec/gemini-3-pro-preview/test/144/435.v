Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4674/7436"; "44534/3844"] -> x1=4674, x2=7436, n1=44534, n2=3844
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4674 7436 44534 3844 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (4674 * 44534) mod (7436 * 3844) *)
    (* This evaluates to 8064028, which is not 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.