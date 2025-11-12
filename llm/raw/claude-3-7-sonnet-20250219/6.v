
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Import ListNotations.

Definition valid_parens_group (s : string) : Prop :=
  (* s consists only of '(' and ')' characters
     and the parentheses are balanced. *)
  let fix aux (i : nat) (cnt : nat) : option nat :=
      match i with
      | 0 => Some cnt
      | S i' =>
        let c := String.get (String.length s - i) s in
        match c with
        | Some "(" => aux i' (S cnt)
        | Some ")" =>
          match cnt with
          | 0 => None
          | S cnt' => aux i' cnt'
          end
        | _ => None
        end
      end
  in aux (String.length s) 0 = Some 0.

Definition max_nesting_depth (s : string) : nat :=
  let fix aux (i : nat) (cnt maxd : nat) : nat :=
      match i with
      | 0 => maxd
      | S i' =>
        let c := String.get (String.length s - i) s in
        match c with
        | Some "(" => aux i' (S cnt) (Nat.max maxd (S cnt))
        | Some ")" => aux i' (cnt - 1) maxd
        | _ => aux i' cnt maxd
        end
      end
  in aux (String.length s) 0 0.

Definition parse_nested_parens_spec (input : string) (output : list nat) : Prop :=
  let groups := String.split " " input in
  output = map max_nesting_depth (filter (fun s => negb (String.eqb s "")) groups) /\
  Forall valid_parens_group (filter (fun s => negb (String.eqb s "")) groups).
