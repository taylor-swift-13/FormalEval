Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
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

(* Test setup parameters *)
Parameter AnyInt : Z -> Any.
Parameter AnyList : list Any -> Any.
Parameter AnyStr : string -> Any.
Parameter AnyBool : bool -> Any.

Axiom IsInt_AnyInt : forall z, IsInt (AnyInt z) z.
Axiom NotIsInt_AnyList : forall l z, ~ IsInt (AnyList l) z.

Example test_filter_integers_mixed : 
  filter_integers_spec 
    [AnyInt 1%Z; AnyList []; AnyList []; AnyInt 8%Z; AnyList [AnyInt 5%Z]; 
     AnyList [AnyInt 7%Z; AnyInt 3%Z; AnyInt 8%Z]; AnyInt 9%Z; AnyInt 9%Z; 
     AnyList [AnyStr ""; AnyBool false]; AnyList [AnyInt 7%Z; AnyInt 3%Z; AnyInt 8%Z]] 
    [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z).
  - apply IsInt_AnyInt.
  - apply fir_cons_nonint.
    + apply NotIsInt_AnyList.
    + apply fir_cons_nonint.
      * apply NotIsInt_AnyList.
      * apply fir_cons_int with (n := 8%Z).
        -- apply IsInt_AnyInt.
        -- apply fir_cons_nonint.
           ++ apply NotIsInt_AnyList.
           ++ apply fir_cons_nonint.
              ** apply NotIsInt_AnyList.
              ** apply fir_cons_int with (n := 9%Z).
                 --- apply IsInt_AnyInt.
                 --- apply fir_cons_int with (n := 9%Z).
                     +++ apply IsInt_AnyInt.
                     +++ apply fir_cons_nonint.
                         *** apply NotIsInt_AnyList.
                         *** apply fir_cons_nonint.
                             ---- apply NotIsInt_AnyList.
                             ---- apply fir_nil.
Qed.