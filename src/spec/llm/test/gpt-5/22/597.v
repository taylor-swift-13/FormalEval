Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition Any := option Z.
Definition int := Z.
Definition IsInt (v : Any) (n : int) : Prop := v = Some n.
Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm. unfold IsInt in *. inversion Hn; inversion Hm; congruence.
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

Example test_case_nonempty:
  filter_integers_spec
    [Some 1%Z; Some 2%Z; Some 3%Z; None; Some 4%Z; Some 5%Z; None; Some 6%Z]
    [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [reflexivity|].
  eapply fir_cons_int; [reflexivity|].
  eapply fir_cons_int; [reflexivity|].
  eapply fir_cons_nonint; [intros n H; unfold IsInt in H; discriminate|].
  eapply fir_cons_int; [reflexivity|].
  eapply fir_cons_int; [reflexivity|].
  eapply fir_cons_nonint; [intros n H; unfold IsInt in H; discriminate|].
  eapply fir_cons_int; [reflexivity|].
  constructor.
Qed.