Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameters v6 v1 v7a v7b non1 non2 non3 non4 non5 : Any.
Axiom IsInt_v6 : IsInt v6 6%Z.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v7a : IsInt v7a 7%Z.
Axiom IsInt_v7b : IsInt v7b 7%Z.
Axiom NonInt_non1 : forall n, ~ IsInt non1 n.
Axiom NonInt_non2 : forall n, ~ IsInt non2 n.
Axiom NonInt_non3 : forall n, ~ IsInt non3 n.
Axiom NonInt_non4 : forall n, ~ IsInt non4 n.
Axiom NonInt_non5 : forall n, ~ IsInt non5 n.

Example test_case_new:
  filter_integers_spec
    [v6; v1; non1; non2; non3; non4; v7a; non5; v7b]
    [6%Z; 1%Z; 7%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v6|].
  eapply fir_cons_int; [apply IsInt_v1|].
  eapply fir_cons_nonint; [apply NonInt_non1|].
  eapply fir_cons_nonint; [apply NonInt_non2|].
  eapply fir_cons_nonint; [apply NonInt_non3|].
  eapply fir_cons_nonint; [apply NonInt_non4|].
  eapply fir_cons_int; [apply IsInt_v7a|].
  eapply fir_cons_nonint; [apply NonInt_non5|].
  eapply fir_cons_int; [apply IsInt_v7b|].
  constructor.
Qed.