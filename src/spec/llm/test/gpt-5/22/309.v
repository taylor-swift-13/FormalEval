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

Parameter eight : int.
Notation "8%Z" := eight.

Parameter aList : Any.
Parameter aInt : Any.

Axiom NonInt_aList : forall n, ~ IsInt aList n.
Axiom IsInt_aInt_eight : IsInt aInt eight.

Notation "[[[6%Z; 5%Z; 5%Z; 5%Z]; 8%Z; [6%Z; 5%Z; 5%Z; 5%Z]; [6%Z; 5%Z; 5%Z; 5%Z]; [6%Z; 5%Z; 5%Z; 5%Z]]]" := ([aList; aInt; aList; aList; aList] : list Any).

Example test_case_new: filter_integers_spec [[[6%Z; 5%Z; 5%Z; 5%Z]; 8%Z; [6%Z; 5%Z; 5%Z; 5%Z]; [6%Z; 5%Z; 5%Z; 5%Z]; [6%Z; 5%Z; 5%Z; 5%Z]]] [8%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - intros n. apply NonInt_aList.
  - apply fir_cons_int with (n:=8%Z).
    + apply IsInt_aInt_eight.
    + apply fir_cons_nonint.
      * intros n. apply NonInt_aList.
      * apply fir_cons_nonint.
        { intros n. apply NonInt_aList. }
        { apply fir_cons_nonint.
          - intros n. apply NonInt_aList.
          - apply fir_nil.
        }
Qed.