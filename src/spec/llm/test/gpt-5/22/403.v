Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

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

Parameter v1 : Any.
Parameter vlist1 : Any.
Parameter vlist2 : Any.
Parameter vlist3a : Any.
Parameter vlist3b : Any.
Parameter vlist4 : Any.
Parameter v9 : Any.
Parameter v1b : Any.
Parameter v1c : Any.
Parameter v9b : Any.
Parameter vlist3c : Any.

Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom NonInt_vlist1 : forall n, ~ IsInt vlist1 n.
Axiom NonInt_vlist2 : forall n, ~ IsInt vlist2 n.
Axiom NonInt_vlist3a : forall n, ~ IsInt vlist3a n.
Axiom NonInt_vlist3b : forall n, ~ IsInt vlist3b n.
Axiom NonInt_vlist4 : forall n, ~ IsInt vlist4 n.
Axiom IsInt_v9 : IsInt v9 9%Z.
Axiom IsInt_v1b : IsInt v1b 1%Z.
Axiom IsInt_v1c : IsInt v1c 1%Z.
Axiom IsInt_v9b : IsInt v9b 9%Z.
Axiom NonInt_vlist3c : forall n, ~ IsInt vlist3c n.

Example test_case_new: filter_integers_spec
  [v1; vlist1; vlist2; vlist3a; vlist3b; vlist4; v9; v1b; v1c; v9b; vlist3c]
  [1%Z; 9%Z; 1%Z; 1%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1|].
  eapply fir_cons_nonint; [apply NonInt_vlist1|].
  eapply fir_cons_nonint; [apply NonInt_vlist2|].
  eapply fir_cons_nonint; [apply NonInt_vlist3a|].
  eapply fir_cons_nonint; [apply NonInt_vlist3b|].
  eapply fir_cons_nonint; [apply NonInt_vlist4|].
  eapply fir_cons_int; [apply IsInt_v9|].
  eapply fir_cons_int; [apply IsInt_v1b|].
  eapply fir_cons_int; [apply IsInt_v1c|].
  eapply fir_cons_int; [apply IsInt_v9b|].
  eapply fir_cons_nonint; [apply NonInt_vlist3c|].
  apply fir_nil.
Qed.