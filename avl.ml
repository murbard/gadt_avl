(* Tail recursive implementation of AVL trees with a GADT and a zipper *)

(* Peano integers type for the GADT *)
type z = Z
type 'n s = S of 'n

(* A node in the AVL tree *)
type ('a, 'n) node =
  | Leaf : ('a, z) node     
  | Balanced   : {left: ('a, 'm)   node; key: 'a; count: int; right: ('a, 'm) node} -> ('a, 'm s) node
  | LeftHeavy  : {left: ('a, 'm s) node; key: 'a; count: int; right: ('a, 'm) node} -> ('a, 'm s s) node
  | RightHeavy : {left: ('a, 'm)   node; key: 'a; count: int; right: ('a, 'm s) node} -> ('a, 'm s s) node

(* A trail / path of node traversed from the top of the tree to a given point. Used to build a zipper *)
type ('a, 'l, 'h) trail =
  | Top             : ('a, z, 'h) trail
        
  | Balanced_Right   : {key: 'a; count: int; left:  ('a,   'h) node; trail: ('a, 'l,   'h s) trail} -> ('a, 'l s, 'h) trail
  | Balanced_Left    : {key: 'a; count: int; right: ('a,   'h) node; trail: ('a, 'l,   'h s) trail} -> ('a, 'l s, 'h) trail
        
  | LeftHeavy_Right  : {key: 'a; count: int; left:  ('a, 'h s) node; trail: ('a, 'l, 'h s s) trail} -> ('a, 'l s, 'h) trail
  | RightHeavy_Left  : {key: 'a; count: int; right: ('a, 'h s) node; trail: ('a, 'l, 'h s s) trail} -> ('a, 'l s, 'h) trail
        
  | LeftHeavy_Left   : {key: 'a; count: int; right: ('a,   'h) node; trail: ('a, 'l, 'h s s) trail} -> ('a, 'l s, 'h s) trail
  | RightHeavy_Right : {key: 'a; count: int; left:  ('a,   'h) node; trail: ('a, 'l, 'h s s) trail} -> ('a, 'l s, 'h s) trail

(* A node after an insertion operation took place. Keeps track of whether the height of the subtree increased
   or not so we know whether and how to rebalance *)
type ('a, 'n) node_insert =
  | Grew of ('a, 'n s) node
  | Same of ('a,   'n) node

(* existential type representing a zipper as a pair between the node we're focused on and the trail to get
   to that node *)
type 'a ex_zipper =
  | Ex_Zipper : ('a, 'h) node * ('a, 'l, 'h) trail -> 'a ex_zipper

(* like a zipper, but where we have a node_insert because we inserted something and are zipping back up *)
type 'a ex_insert_zipper =
  | Ex_Insert_Zipper : int * ('a, 'h) node_insert * ('a, 'l, 'h) trail -> 'a ex_insert_zipper 

(* existential type to work with trees of height unknown to the typechecker *)
type 'a ex_node =
  | Node : ('a, 'n) node -> 'a ex_node

(* auxiliary function to access the count field without doing a pattern match *)
let get_count : type n . ('a, n) node -> int = function
  | Leaf -> 0
  | Balanced { count; _ } -> count
  | LeftHeavy { count; _ } -> count
  | RightHeavy { count; _ } -> count

(* Search through the tree and return a zipper that focuses on a value or on where
   that value would be inserted *)
let rec locate : 'a -> 'a ex_zipper -> 'a ex_zipper = fun x -> function
  | Ex_Zipper (Balanced {left; key; count; right}, trail) as zipper ->
    if x < key then
      locate x (Ex_Zipper (left, Balanced_Left {key; count; right; trail}))
    else if x > key then
      locate x (Ex_Zipper (right, Balanced_Right {key; count; left; trail}))
    else
      zipper
  | Ex_Zipper (LeftHeavy {left; key; count; right}, trail) as zipper ->
    if x < key then
      locate x (Ex_Zipper (left, LeftHeavy_Left {key; count; right; trail}))
    else if x > key then
      locate x (Ex_Zipper (right, LeftHeavy_Right {key; count; left; trail}))
    else
      zipper
  | Ex_Zipper (RightHeavy {left; key; count; right}, trail) as zipper ->
    if x < key then
      locate x (Ex_Zipper (left, RightHeavy_Left {key; count; right; trail}))
    else if x > key then
      locate x (Ex_Zipper (right, RightHeavy_Right {key; count; left; trail}))
    else
      zipper
  | Ex_Zipper (Leaf, _) as zipper -> zipper

(* Zip back up after an insertion *)
let rec zip_up : 'a ex_insert_zipper -> 'a ex_insert_zipper = function

  (* We have reached the top, nothing left to do *)
  | Ex_Insert_Zipper (_, _, Top) as zipper -> zipper

  (* Easy cass which do not require a rotation *)
  | Ex_Insert_Zipper (added, ileft, Balanced_Left {key; count; right; trail}) -> (
      match ileft with
      | Same left -> Ex_Insert_Zipper (added, Same (Balanced {left; count = count + added; key; right}), trail) |> zip_up
      | Grew left -> Ex_Insert_Zipper (added, Grew (LeftHeavy {left; count = count + added; key; right}), trail) |> zip_up
    )
    
  | Ex_Insert_Zipper (added, iright, Balanced_Right {key; count; left; trail}) -> (
      match iright with
      | Same right -> Ex_Insert_Zipper (added, Same (Balanced {left; count = count + added; key; right}), trail) |> zip_up
      | Grew right -> Ex_Insert_Zipper (added, Grew (RightHeavy {left; count = count + added; key; right}), trail) |> zip_up
    )

  | Ex_Insert_Zipper (added, ileft, RightHeavy_Left {key; count; right; trail}) -> (
      match ileft with
      | Same left -> Ex_Insert_Zipper (added, Same (RightHeavy {left; key; count = count + added; right}), trail) |> zip_up
      | Grew left -> Ex_Insert_Zipper (added, Same (Balanced {left; key; count = count + added; right}), trail) |> zip_up
    )

  | Ex_Insert_Zipper (added, iright, LeftHeavy_Right {key; count; left; trail}) -> (
      match iright with
      | Same right -> Ex_Insert_Zipper (added, Same (LeftHeavy {left; key; count = count + added; right}), trail) |> zip_up
      | Grew right -> Ex_Insert_Zipper (added, Same (Balanced {left; key; count = count + added; right}), trail) |> zip_up
    )

  | Ex_Insert_Zipper (added, ileft, LeftHeavy_Left {key; count; right; trail}) -> (

      match ileft with
      (* no rotation needed *)
      | Same left -> Ex_Insert_Zipper (added, Same (LeftHeavy { left; key; count = count + added; right}), trail) |> zip_up

      | Grew left -> (match left with
          | Balanced _ -> assert false (* unreachable because that would mean we inserted two keys *)

          (* single rotation sufficient 
             ((ll, lk, lr), k, r) -> (ll, lk, (lr, k, r))
          *)
          | LeftHeavy {left = left_left; key = left_key; right = left_right; _} ->          
            Ex_Insert_Zipper (added, Same (Balanced {
                left = left_left;
                key = left_key;
                count = count + added;
                right = Balanced {left = left_right; key; count = (get_count left_right) + (get_count right) + 1; right}}
              ), trail) |> zip_up

          (* doube rotation needed
             ((ll, lk, (lrl, lrk, lrr)),k,r)->  ((ll,lk,lrl),lrk,(lrr,k,r))
          *)
          | RightHeavy {left = left_left; key = left_key; right = left_right; _} -> (
              match left_right with
              | LeftHeavy {left = left_right_left; key = left_right_key; right = left_right_right; _} ->
                Ex_Insert_Zipper (added, Same ( Balanced {
                    left = Balanced {
                        left = left_left;
                        key = left_key;
                        count = (get_count left_left) + (get_count left_right_left) + 1;
                        right = left_right_left};
                    key = left_right_key;
                    count = count + added;
                    right = RightHeavy {
                        left = left_right_right;
                        key = key;
                        count = (get_count left_right_right) + (get_count right) + 1;
                        right = right}}
                  ), trail) |> zip_up

              (* double rotation needed 
                 ((ll,lk,(lrl, lrk, lrr)),k,r) -> (((ll,lk,lrl),lrk,(lrr,kr,r))
              *)
              | RightHeavy {left = left_right_left; key = left_right_key; right = left_right_right; _ } ->
                Ex_Insert_Zipper (added, Same ( Balanced {
                    left = LeftHeavy {
                        left = left_left;
                        key = left_key;
                        count = (get_count left_left) + (get_count left_right_left) + 1;
                        right = left_right_left};
                    key =  left_right_key;
                    count = count + added;
                    right = Balanced {
                        left = left_right_right;
                        key = key;
                        count = (get_count left_right_right) + (get_count right) + 1;
                        right}}
                  ), trail) |> zip_up
                              
              | Balanced {left = left_right_left; key = left_right_key; right = left_right_right; _ } ->                
                Ex_Insert_Zipper (added, Same (Balanced {
                    left = Balanced {
                        left = left_left;
                        key = left_key;
                        count = (get_count left_left) + (get_count left_right_left) + 1;
                        right = left_right_left};
                    key = left_right_key;
                    count = count + added;
                    right = Balanced {
                        left = left_right_right;
                        key = key;
                        count = (get_count left_right_right) + (get_count right) + 1;
                        right}}
                  ), trail) |> zip_up
            )))
    
  | Ex_Insert_Zipper (added, iright, RightHeavy_Right {key; count; left; trail}) -> (
     match iright with
      | Same right -> Ex_Insert_Zipper (added, Same (RightHeavy {left; key; right; count = count + added}), trail) |> zip_up
      | Grew right ->
        (match right with
         (* unreachable because that would mean we inserted two keys *)
         | Balanced _ -> assert false
           
            (*
               (l,k,(rl,rk,rr)) -> ((l,k,rl),rk,rr) *)
         | RightHeavy {left = right_left; key = right_key; right = right_right; _} ->          
           Ex_Insert_Zipper (added, Same (Balanced {
               left = Balanced {
                   left = left;
                   key;
                   count = (get_count left) + (get_count right_left) + 1;
                   right = right_left};
               key = right_key;                  
               count = count + added;
               right = right_right}
             ), trail) |> zip_up

         (* (l,k,((rll, rlk, rlr),rk,rr)) -> ((l,k,rll),rlk,(rlr,rk,rr)) *)
         | LeftHeavy {left = right_left; key = right_key;  right = right_right; _} -> (
             match right_left with
          | RightHeavy {left = right_left_left; key = right_left_key; right = right_left_right; _} ->
            Ex_Insert_Zipper (added,  Same (Balanced {
                  left = LeftHeavy {
                    left;
                    key;
                    right = right_left_left;
                    count = (get_count left) + (get_count right_left_left) + 1
                  };
                  key = right_left_key;
                  count = count + added;
                  right = Balanced {
                      left = right_left_right;
                      key = right_key;
                      count = (get_count right_left_right) + (get_count right_right);
                      right = right_right}}
              ), trail) |> zip_up            
            
          (* (l,k,((rll, rlk, rlr),rk,rr)) -> ((l,k,rll),rlk,(rlr,rk,rr)) *)
          | LeftHeavy {left = right_left_left; key = right_left_key; right = right_left_right; _} ->
            Ex_Insert_Zipper (added, Same ( Balanced {
                left = Balanced {
                    left;
                    key;
                    count = (get_count left) + (get_count right_left_left);
                    right = right_left_left;
                  };                
                key = right_left_key;
                count = count + added;
                right = RightHeavy {
                    left = right_left_right;
                    key = right_key;
                    count = (get_count right_left_right) + (get_count right_right);
                    right = right_right                    
                  }}
              ), trail) |> zip_up

             
          (* (l,k,((rll, rlk, rlr),rk,rr)) -> ((l,k,rll),rlk,(rlr,rk,rr)) *)
          | Balanced {left = right_left_left; key = right_left_key; right = right_left_right; _ } ->                
            Ex_Insert_Zipper (added, Same ( Balanced {          
                left = Balanced {
                    left = left;
                    key;
                    count = (get_count left) + (get_count right_left_left) + 1;
                    right = right_left_left
                  };
                key = right_left_key;
                count = (get_count left) + (get_count right_left_left);
                right = Balanced {
                    left = right_left_right;
                    key = right_key;
                    count = (get_count right_left_right) + (get_count right_right) + 1;
                    right = right_right}}
              ), trail) |> zip_up
           )))

let insert : 'a -> 'a ex_node -> 'a ex_node = fun x -> fun (Node node) ->  
  let zipper = Ex_Zipper (node, Top) in
  let zipper = 
    match locate x zipper  with
    | Ex_Zipper (Leaf, trail) -> Ex_Insert_Zipper (1, Grew (Balanced {left = Leaf; key = x; right = Leaf; count = 1}), trail)
    | _ -> assert false
  in
  let zipper = zip_up zipper in
  match zipper with
  | Ex_Insert_Zipper(_, Grew node, Top) -> Node node
  | Ex_Insert_Zipper(_, Same node, Top) -> Node node
  | _ -> assert false

