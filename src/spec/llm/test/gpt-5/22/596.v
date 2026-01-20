Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition Any := Z.
Definition int := Z.
Definition IsInt (v : Any) (n : int) : Prop := v = n.
Lemma IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.
Proof.
  intros v n m Hn Hm.
  unfold IsInt in *.
  subst.
  reflexivity.
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

Example test_case: filter_integers_spec [3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z] [3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  eapply fir_cons_int; [unfold IsInt; reflexivity |].
  constructor.
Qed.