Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive Any : Type :=
| AInt : Z -> Any
| AList : list Any -> Any
| AString : string -> Any.

Definition int := Z.

Definition IsInt (v : Any) (n : int) : Prop :=
  match v with
  | AInt z => z = n
  | _ => False
  end.

Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  destruct v; simpl in Hn, Hm; try contradiction.
  now subst.
Qed.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Example test_case_mixed:
  filter_integers_spec
    [AInt 1%Z; AInt 10%Z; AList [AInt 3%Z]; AList [AInt 2%Z; AString "3"]; AList [AInt 3%Z]; AList [AInt 5%Z; AInt 6%Z]; AList [AInt 7%Z; AInt 2%Z]; AInt 8%Z]
    [1%Z; 10%Z; 8%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [simpl; reflexivity|].
  eapply fir_cons_int; [simpl; reflexivity|].
  eapply fir_cons_nonint; [intros n H; simpl in H; contradiction|].
  eapply fir_cons_nonint; [intros n H; simpl in H; contradiction|].
  eapply fir_cons_nonint; [intros n H; simpl in H; contradiction|].
  eapply fir_cons_nonint; [intros n H; simpl in H; contradiction|].
  eapply fir_cons_nonint; [intros n H; simpl in H; contradiction|].
  eapply fir_cons_int; [simpl; reflexivity|].
  constructor.
Qed.