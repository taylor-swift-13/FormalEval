Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Require Import Lia.

Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

Example test_case_1 : forall number need remaining result,
  problem_159_pre number need remaining ->
  problem_159_spec number need remaining result ->
  number = 7%Z -> need = 7%Z -> remaining = 6%Z ->
  result = [13%Z; 0%Z].
Proof.
  intros number need remaining result Hpre Hspec Hnumber Hneed Hremaining.
  unfold problem_159_pre in Hpre.
  unfold problem_159_spec in Hspec.
  subst number need remaining.
  simpl in *.
  destruct Hspec as [[Hge Hresult] | [Hlt Hresult]].
  - lia. (* This case is impossible as 6 is not greater than or equal to 7 *)
  - rewrite Hresult. reflexivity.
Qed.