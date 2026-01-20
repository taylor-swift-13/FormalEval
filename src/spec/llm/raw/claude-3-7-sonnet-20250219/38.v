
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition encode_cyclic_spec (s encoded : string) : Prop :=
  let groups := 
    let n := String.length s in
    let num_groups := (n + 2) / 3 in
    (* split s into groups of length 3, last group may be shorter *)
    let fix split_groups i :=
      match i with
      | 0 => []
      | S i' =>
        let start := 3 * i' in
        let end_ := if 3 * i' + 3 <= n then 3 * i' + 3 else n in
        let group := substring start (end_ - start) s in
        split_groups i' ++ [group]
      end
    in split_groups num_groups
  in
  let cycled_groups := 
    map (fun group =>
      if String.length group =? 3 then
        (* cycle group: group[1:] + group[0] *)
        let c1 := String.get 1 group in
        let c2 := String.get 2 group in
        let c0 := String.get 0 group in
        match c0, c1, c2 with
        | Some ch1, Some ch2, Some ch0 =>
          String.append (String.append (String.make 1 ch1) (String.make 1 ch2)) (String.make 1 ch0)
        | _, _, _ => group
        end
      else group) groups
  in
  encoded = String.concat "" cycled_groups.

Definition decode_cyclic_spec (s decoded : string) : Prop :=
  let groups :=
    let n := String.length s in
    let num_groups := (n + 2) / 3 in
    let fix split_groups i :=
      match i with
      | 0 => []
      | S i' =>
        let start := 3 * i' in
        let end_ := if 3 * i' + 3 <= n then 3 * i' + 3 else n in
        let group := substring start (end_ - start) s in
        split_groups i' ++ [group]
      end
    in split_groups num_groups
  in
  let decycled_groups :=
    map (fun group =>
      if String.length group =? 3 then
        (* decode group: group[2] + group[:2] *)
        let c2 := String.get 2 group in
        let c0 := String.get 0 group in
        let c1 := String.get 1 group in
        match c2, c0, c1 with
        | Some ch2, Some ch0, Some ch1 =>
          String.append (String.make 1 ch2) (String.append (String.make 1 ch0) (String.make 1 ch1))
        | _, _, _ => group
        end
      else group) groups
  in
  decoded = String.concat "" decycled_groups.
