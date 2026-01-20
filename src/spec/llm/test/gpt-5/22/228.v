Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter FromZ : Z -> Any.
Parameter FromString : string -> Any.
Parameter FromList : list Any -> Any.
Axiom IsInt_FromList_false : forall xs n, ~ IsInt (FromList xs) n.

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

Example test_case_nested_lists:
  filter_integers_spec
    [ FromList [ FromZ 1%Z ; FromString "2" ]
    ; FromList [ FromString "3" ; FromString "33" ; FromZ 4%Z ]
    ; FromList []
    ; FromList [ FromString "seven" ; FromString "8" ]
    ; FromList []
    ; FromList [] ]
    [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact (IsInt_FromList_false [FromZ 1%Z; FromString "2"]).
  - eapply fir_cons_nonint.
    + exact (IsInt_FromList_false [FromString "3"; FromString "33"; FromZ 4%Z]).
    + eapply fir_cons_nonint.
      * exact (IsInt_FromList_false []).
      * eapply fir_cons_nonint.
        { exact (IsInt_FromList_false [FromString "seven"; FromString "8"]). }
        { eapply fir_cons_nonint.
          { exact (IsInt_FromList_false []). }
          { eapply fir_cons_nonint.
            { exact (IsInt_FromList_false []). }
            { constructor. } } }
Qed.