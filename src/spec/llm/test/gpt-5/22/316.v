Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameter a10 : Any.
Parameter aNil : Any.
Parameter aList5 : Any.
Parameter aList9a : Any.
Parameter a9a : Any.
Parameter aNil2 : Any.
Parameter aList9b : Any.
Parameter aBoolList : Any.
Parameter a9b : Any.
Parameter aList9c : Any.

Parameter ten : int.
Parameter nine : int.

Axiom IsInt_a10 : IsInt a10 ten.
Axiom IsInt_a9a : IsInt a9a nine.
Axiom IsInt_a9b : IsInt a9b nine.

Axiom NotInt_aNil : forall n, ~ IsInt aNil n.
Axiom NotInt_aList5 : forall n, ~ IsInt aList5 n.
Axiom NotInt_aList9a : forall n, ~ IsInt aList9a n.
Axiom NotInt_aNil2 : forall n, ~ IsInt aNil2 n.
Axiom NotInt_aList9b : forall n, ~ IsInt aList9b n.
Axiom NotInt_aBoolList : forall n, ~ IsInt aBoolList n.
Axiom NotInt_aList9c : forall n, ~ IsInt aList9c n.

Notation "10%Z" := ten.
Notation "9%Z" := nine.

Example test_case_new: filter_integers_spec [a10; aNil; aList5; aList9a; a9a; aNil2; aList9b; aBoolList; a9b; aList9c] [10%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_a10 |].
  eapply fir_cons_nonint; [apply NotInt_aNil |].
  eapply fir_cons_nonint; [apply NotInt_aList5 |].
  eapply fir_cons_nonint; [apply NotInt_aList9a |].
  eapply fir_cons_int; [apply IsInt_a9a |].
  eapply fir_cons_nonint; [apply NotInt_aNil2 |].
  eapply fir_cons_nonint; [apply NotInt_aList9b |].
  eapply fir_cons_nonint; [apply NotInt_aBoolList |].
  eapply fir_cons_int; [apply IsInt_a9b |].
  eapply fir_cons_nonint; [apply NotInt_aList9c |].
  apply fir_nil.
Qed.