def N : Nat := 4      -- size of environment

-- Enumerations
inductive Direction
  | up
  | down
  | left
  | right

def Direction.to_string (d : Direction) : String :=
  match d with
  | .up => "up"
  | .down => "down"
  | .left => "left"
  | .right => "right"

open Direction

inductive State
  | unknown
  | safe
  | pit
  | wumpus
  | breeze
  | stench
  | stench_breeze
  | pit_stench
  | wumpus_breeze

def State.to_string (s : State) : String :=
  match s with
  | .unknown => "unknown"
  | .safe => "safe"
  | .pit => "pit"
  | .wumpus => "wumpus"
  | .breeze => "breeze"
  | .stench => "stench"
  | .stench_breeze => "st_brz"
  | .pit_stench => "pit_stench"
  | .wumpus_breeze => "wumpus_breeze"

instance : BEq State where
  beq a b := match a, b with
  | .unknown, .unknown => true
  | .safe, .safe => true
  | .pit, .pit => true
  | .wumpus, .wumpus => true
  | .breeze, .breeze => true
  | .stench, .stench => true
  | .stench_breeze, .stench_breeze => true
  | .pit_stench, .pit_stench => true
  | .wumpus_breeze, .wumpus_breeze => true
  | _, _ => false

open State

-- Position
structure Pos where
  x : Nat
  y : Nat
deriving Repr, BEq

def Pos.move (p : Pos) (direction : Direction) : Pos :=
  match direction with
  | up => { x := p.x, y := p.y + 1 }
  | down => { x := p.x, y := p.y - 1 }
  | left => { x := p.x - 1, y := p.y }
  | right => { x := p.x + 1, y := p.y }

def Pos.adjacent (p q : Pos) : Bool :=
  p.x = q.x + 1 ∧ p.y = q.y ∨ p.x = q.x ∧ p.y = q.y + 1 ∨ p.x = q.x - 1 ∧ p.y = q.y ∨ p.x = q.x ∧ p.y = q.y - 1

def is_valid_pos (p : Pos) : Bool :=
  p.x >= 0 ∧ p.y >= 0 ∧ p.x < N ∧ p.y < N


-- Environment
structure Environment where
  map : Array (Array State) :=
    #[#[safe,   breeze,        pit,    breeze],
      #[stench, safe,          breeze, safe],
      #[wumpus, stench_breeze, pit,    breeze],
      #[stench, safe,          breeze, pit]]

  get_state (p : Pos) : State :=
    match map[p.y]? with
    | none => safe
    | some row =>
      match row[p.x]? with
      | none => safe
      | some state => state

  set_state (p : Pos) (s : State) (map : Array (Array State)) : Array (Array State) :=
    map.set! p.y (map[p.y]!.set! p.x s)

  set_shot_env (p : Pos) (map : Array (Array State)) : Array (Array State) :=
    let new_map := map
    let pos_up := Pos.move p up
    let pos_down := Pos.move p down
    let pos_left := Pos.move p left
    let pos_right := Pos.move p right
    if get_state p == wumpus then
      let new_map := set_state p safe new_map
      let new_map := [pos_up, pos_down, pos_left, pos_right]
        |>.foldl (fun m p =>
            match get_state p with
            | stench => set_state p safe m
            | stench_breeze => set_state p breeze m
            | _ => m) new_map
      new_map
    else -- wumpus_breeze
      let new_map := set_state p breeze new_map
      let new_map := [pos_up, pos_down, pos_left, pos_right]
        |>.foldl (fun m p =>
            match get_state p with
            | stench => set_state p safe m
            | stench_breeze => set_state p breeze m
            | _ => m) new_map
      new_map

def init_environment : Environment := {}

def wumpus_pos : Pos := { x := 0, y := 2 }

-- Agent
structure Agent where
  direction : Direction := up
  pos : Pos :=  { x := 0, y := 0 }
  is_shot : Bool := false
  first_stench : Pos := { x := 0, y := 0 }

  env : Environment := init_environment

  state_map : Array (Array State) :=
    #[#[safe,    unknown, unknown, unknown],
      #[unknown, unknown, unknown, unknown],
      #[unknown, unknown, unknown, unknown],
      #[unknown, unknown, unknown, unknown]]
  get_visited (p : Pos) : State :=
    match state_map[p.y]? with
    | none => unknown
    | some row =>
      match row[p.x]? with
      | none => unknown
      | some state => state
  set_visited (p : Pos) (b : State) (map : Array (Array State)) : Array (Array State) :=
    map.set! p.y (map[p.y]!.set! p.x b)

  direction_map : Array (Array Direction) :=
    #[#[up, up, up, up],
      #[up, up, up, up],
      #[up, up, up, up],
      #[up, up, up, up]]
  get_direction (p : Pos) : Direction :=
    match direction_map[p.y]? with
    | none => up
    | some row =>
      match row[p.x]? with
      | none => up
      | some direction => direction
  set_direction (p : Pos) (d : Direction) (map : Array (Array Direction)) : Array (Array Direction) :=
    map.set! p.y (map[p.y]!.set! p.x d)

  shot (d : Direction) : Bool :=
    match d with
    | up =>
      if wumpus_pos.y > pos.y then
        true
      else
        false
    | down =>
      if wumpus_pos.y < pos.y then
        true
      else
        false
    | left =>
      if wumpus_pos.x < pos.x then
        true
      else
        false
    | right =>
      if wumpus_pos.x > pos.x then
        true
      else
        false

  find_contradiction (p : Pos) : Bool :=
    let p_up := Pos.move p up
    let p_down := Pos.move p down
    let p_left := Pos.move p left
    let p_right := Pos.move p right
    if (get_visited p_up == breeze ∨ get_visited p_down == breeze ∨ get_visited p_left == breeze ∨ get_visited p_right == breeze) ∧
       (get_visited p_up == stench ∨ get_visited p_down == stench ∨ get_visited p_left == stench ∨ get_visited p_right == stench) then
      true
    else
      false

  get_pit (p : Pos) : Pos :=
    let p_up := Pos.move p up
    let p_down := Pos.move p down
    let p_left := Pos.move p left
    let p_right := Pos.move p right
    if ¬ env.get_state p == breeze ∨ get_visited p_up == pit ∨ get_visited p_down == pit ∨ get_visited p_left == pit ∨ get_visited p_right == pit then
      p
    else if is_valid_pos p_up ∧ get_visited p_up == unknown ∧
            (¬ is_valid_pos p_down ∨ ¬ get_visited p_down == unknown) ∧
            (¬ is_valid_pos p_left ∨ ¬ get_visited p_left == unknown) ∧
            (¬ is_valid_pos p_right ∨ ¬ get_visited p_right == unknown) then
      p_up
    else if is_valid_pos p_down ∧ get_visited p_down == unknown ∧
            (¬ is_valid_pos p_up ∨ ¬ get_visited p_up == unknown) ∧
            (¬ is_valid_pos p_left ∨ ¬ get_visited p_left == unknown) ∧
            (¬ is_valid_pos p_right ∨ ¬ get_visited p_right == unknown) then
      p_down
    else if is_valid_pos p_left ∧ get_visited p_left == unknown ∧
            (¬ is_valid_pos p_up ∨ ¬ get_visited p_up == unknown) ∧
            (¬ is_valid_pos p_down ∨ ¬ get_visited p_down == unknown) ∧
            (¬ is_valid_pos p_right ∨ ¬ get_visited p_right == unknown) then
      p_left
    else if is_valid_pos p_right ∧ get_visited p_right == unknown ∧
            (¬ is_valid_pos p_up ∨ ¬ get_visited p_up == unknown) ∧
            (¬ is_valid_pos p_down ∨ ¬ get_visited p_down == unknown) ∧
            (¬ is_valid_pos p_left ∨ ¬ get_visited p_left == unknown) then
      p_right
    else
      p

  get_wumpus (p : Pos) : Pos :=
    let p_up := Pos.move p up
    let p_down := Pos.move p down
    let p_left := Pos.move p left
    let p_right := Pos.move p right
    -- two stench have found
    if ¬ first_stench == { x := 0, y := 0 } ∧ ¬ first_stench == p then
      let q := first_stench
      if p.x < q.x then
        if ¬ get_visited { x := p.x, y := q.y } == unknown then
          { x := q.x, y := p.y }
        else if ¬ get_visited { x := q.x, y := p.y } == unknown then
          { x := p.x, y := q.y }
        else if p.y < q.y then
          let p1 := { x := p.x, y := q.y + 1 }
          let p2 := { x := p.x - 1, y := q.y }
          if (is_valid_pos p1 ∧ ¬ get_visited p1 == unknown) ∨ (is_valid_pos p2 ∧ ¬ get_visited p2 == unknown) then
            { x := q.x, y := p.y }
          else
            { x := p.x, y := q.y }
        else -- p.y > q.y
          let p1 := { x := p.x, y := q.y - 1 }
          let p2 := { x := p.x - 1, y := q.y }
          if (is_valid_pos p1 ∧ ¬ get_visited p1 == unknown) ∨ (is_valid_pos p2 ∧ ¬ get_visited p2 == unknown) then
            { x := q.x, y := p.y }
          else
            { x := p.x, y := q.y }
      else -- p.x > q.x
        if ¬ get_visited { x := p.x, y := q.y } == unknown then
          { x := q.x, y := p.y }
        else if ¬ get_visited { x := q.x, y := p.y } == unknown then
          { x := p.x, y := q.y }
        else if p.y < q.y then
          let p1 := { x := p.x, y := q.y + 1 }
          let p2 := { x := p.x + 1, y := q.y }
          if (is_valid_pos p1 ∧ ¬ get_visited p1 == unknown) ∨ (is_valid_pos p2 ∧ ¬ get_visited p2 == unknown) then
            { x := q.x, y := p.y }
          else
            { x := p.x, y := q.y }
        else -- p.y > q.y
          let p1 := { x := p.x, y := q.y - 1 }
          let p2 := { x := p.x + 1, y := q.y }
          if (is_valid_pos p1 ∧ ¬ get_visited p1 == unknown) ∨ (is_valid_pos p2 ∧ ¬ get_visited p2 == unknown) then
            { x := q.x, y := p.y }
          else
            { x := p.x, y := q.y }
    else -- second stench has not found
      if ¬ env.get_state p == stench then
        p
      else if is_valid_pos p_up ∧ get_visited p_up == unknown ∧
              (¬ is_valid_pos p_down ∨ ¬ get_visited p_down == unknown) ∧
              (¬ is_valid_pos p_left ∨ ¬ get_visited p_left == unknown) ∧
              (¬ is_valid_pos p_right ∨ ¬ get_visited p_right == unknown) then
        p_up
      else if is_valid_pos p_down ∧ get_visited p_down == unknown ∧
              (¬ is_valid_pos p_up ∨ ¬ get_visited p_up == unknown) ∧
              (¬ is_valid_pos p_left ∨ ¬ get_visited p_left == unknown) ∧
              (¬ is_valid_pos p_right ∨ ¬ get_visited p_right == unknown) then
        p_down
      else if is_valid_pos p_left ∧ get_visited p_left == unknown ∧
              (¬ is_valid_pos p_up ∨ ¬ get_visited p_up == unknown) ∧
              (¬ is_valid_pos p_down ∨ ¬ get_visited p_down == unknown) ∧
              (¬ is_valid_pos p_right ∨ ¬ get_visited p_right == unknown) then
        p_left
      else if is_valid_pos p_right ∧ get_visited p_right == unknown ∧
              (¬ is_valid_pos p_up ∨ ¬ get_visited p_up == unknown) ∧
              (¬ is_valid_pos p_down ∨ ¬ get_visited p_down == unknown) ∧
              (¬ is_valid_pos p_left ∨ ¬ get_visited p_left == unknown) then
        p_right
      else
        p

  set_shot_state_map (p : Pos) (map : Array (Array State)) : Array (Array State) :=
    let new_map := map
    let pos_up := Pos.move p up
    let pos_down := Pos.move p down
    let pos_left := Pos.move p left
    let pos_right := Pos.move p right
    if get_visited p == wumpus then
      let new_map := set_visited p safe new_map
      let new_map := [pos_up, pos_down, pos_left, pos_right]
        |>.foldl (fun m p =>
            match get_visited p with
            | unknown => m
            | stench => set_visited p safe m
            | stench_breeze => set_visited p breeze m
            | _ => m) new_map
      new_map
    else -- wumpus_breeze
      let new_map := set_visited p breeze new_map
      let new_map := [pos_up, pos_down, pos_left, pos_right]
        |>.foldl (fun m p =>
            match get_visited p with
            | stench => set_visited p safe m
            | stench_breeze => set_visited p breeze m
            | _ => m) new_map
      new_map

def init_agent : Agent :=
  { direction := up, pos := { x := 0, y := 0 }, is_shot := false, first_stench := { x := 0, y := 0 } }

def map_to_string (map : Array (Array State)) : String :=
  "[\n" ++ (map.foldl (
    fun s row =>
      s ++ "\t[" ++ (row.foldl (
        fun s state =>
          s ++ (State.to_string state) ++ "\t"
      ) "") ++ "]\n"
  ) "") ++ "]"

#eval IO.println (map_to_string init_environment.map)

-- Move agent for one step
def step (agent : Agent) : Agent :=
  let state := agent.env.get_state agent.pos
  let agent_up := Pos.move agent.pos up
  let agent_down := Pos.move agent.pos down
  let agent_left := Pos.move agent.pos left
  let agent_right := Pos.move agent.pos right

  match state with
  | safe =>
    -- find a room that is not visited
    if is_valid_pos agent_up ∧ agent.get_visited agent_up == unknown then
      { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
        state_map := agent.set_visited agent_up (agent.env.get_state agent_up) agent.state_map,
        direction_map := agent.set_direction agent_up up agent.direction_map }
    else if is_valid_pos agent_down ∧ agent.get_visited agent_down == unknown then
      { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
        state_map := agent.set_visited agent_down (agent.env.get_state agent_down) agent.state_map ,
        direction_map := agent.set_direction agent_down down agent.direction_map }
    else if is_valid_pos agent_left ∧ agent.get_visited agent_left == unknown then
      { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
        state_map := agent.set_visited agent_left (agent.env.get_state agent_left) agent.state_map,
        direction_map := agent.set_direction agent_left left agent.direction_map }
    else if is_valid_pos agent_right ∧ agent.get_visited agent_right == unknown then
      { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
        state_map := agent.set_visited agent_right (agent.env.get_state agent_right) agent.state_map,
        direction_map := agent.set_direction agent_right right agent.direction_map }
    else
      -- return to the previous position
      match agent.get_direction agent.pos with
      | up => { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                state_map := agent.state_map, direction_map := agent.direction_map }
      | down => { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                  state_map := agent.state_map, direction_map := agent.direction_map }
      | left => { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                  state_map := agent.state_map, direction_map := agent.direction_map }
      | right => { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                   state_map := agent.state_map, direction_map := agent.direction_map }
  | breeze =>
    -- try to find a pit
    let pit_pos := agent.get_pit agent.pos
    if ¬ pit_pos == agent.pos then
      -- find a room that is not visited and set the pit as visited
      if is_valid_pos agent_up ∧ agent.get_visited agent_up == unknown ∧ ¬ pit_pos == agent_up then
        { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited pit_pos pit (agent.set_visited agent_up (agent.env.get_state agent_up) agent.state_map),
          direction_map := agent.set_direction agent_up up agent.direction_map }
      else if is_valid_pos agent_down ∧ agent.get_visited agent_down == unknown ∧ ¬ pit_pos == agent_down then
        { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited pit_pos pit (agent.set_visited agent_down (agent.env.get_state agent_down) agent.state_map),
          direction_map := agent.set_direction agent_down down agent.direction_map }
      else if is_valid_pos agent_left ∧ agent.get_visited agent_left == unknown ∧ ¬ pit_pos == agent_left then
        { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited pit_pos pit (agent.set_visited agent_left (agent.env.get_state agent_left) agent.state_map),
          direction_map := agent.set_direction agent_left left agent.direction_map}
      else if is_valid_pos agent_right ∧ agent.get_visited agent_right == unknown ∧ ¬ pit_pos == agent_right then
        { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited pit_pos pit (agent.set_visited agent_right (agent.env.get_state agent_right) agent.state_map),
          direction_map := agent.set_direction agent_right right agent.direction_map }
      else
        -- return to the previous position
        match agent.get_direction agent.pos with
        | up => { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                  state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
        | down => { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                    state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
        | left => { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                    state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
        | right => { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                     state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
    else
    -- not found
      if is_valid_pos agent_up ∧ agent.find_contradiction agent_up ∧ agent.get_visited agent_up == unknown then
        { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited agent_up (agent.env.get_state agent_up) agent.state_map,
          direction_map := agent.set_direction agent_up up agent.direction_map }
      else if is_valid_pos agent_down ∧ agent.find_contradiction agent_down ∧ agent.get_visited agent_down == unknown then
        { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited agent_down (agent.env.get_state agent_down) agent.state_map,
          direction_map := agent.set_direction agent_down down agent.direction_map }
      else if is_valid_pos agent_left ∧ agent.find_contradiction agent_left ∧ agent.get_visited agent_left == unknown then
        { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited agent_left (agent.env.get_state agent_left) agent.state_map,
          direction_map := agent.set_direction agent_left left agent.direction_map }
      else if is_valid_pos agent_right ∧ agent.find_contradiction agent_right ∧ agent.get_visited agent_right == unknown then
        { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
          state_map := agent.set_visited agent_right (agent.env.get_state agent_right) agent.state_map,
          direction_map := agent.set_direction agent_right right agent.direction_map }
      else
        -- return to the previous position
        match agent.get_direction agent.pos with
        | up => { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                  state_map := agent.state_map, direction_map := agent.direction_map }
        | down => { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                    state_map := agent.state_map, direction_map := agent.direction_map }
        | left => { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                    state_map := agent.state_map, direction_map := agent.direction_map }
        | right => { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := agent.first_stench, env := agent.env,
                     state_map := agent.state_map, direction_map := agent.direction_map }
  | stench =>
    -- try to find a wumpus
    let wumpus_pos := agent.get_wumpus agent.pos
    let first_stench :=
      if agent.first_stench == { x := 0, y := 0 } then
        agent.pos
      else
        agent.first_stench
    if ¬ wumpus_pos == agent.pos then
      -- shot the wumpus
      if agent.pos.x < wumpus_pos.x ∧ agent.shot right then
        { direction := right, pos := agent_right, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_right right agent.direction_map }
      else if agent.pos.x > wumpus_pos.x ∧ agent.shot left then
        { direction := left, pos := agent_left, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_left left agent.direction_map }
      else if agent.pos.y < wumpus_pos.y ∧ agent.shot down then
        { direction := down, pos := agent_down, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_down down agent.direction_map }
      else -- agent.pos.y > wumpus_pos.y ∧ agent.shot up
        { direction := up, pos := agent_up, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_up up agent.direction_map }
    else -- wumpus not found
      if is_valid_pos agent_up ∧ agent.find_contradiction agent_up ∧ agent.get_visited agent_up == unknown then
        { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
          state_map := agent.set_visited agent_up (agent.env.get_state agent_up) agent.state_map,
          direction_map := agent.set_direction agent_up up agent.direction_map }
      else if is_valid_pos agent_down ∧ agent.find_contradiction agent_down ∧ agent.get_visited agent_down == unknown then
        { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
          state_map := agent.set_visited agent_down (agent.env.get_state agent_down) agent.state_map,
          direction_map := agent.set_direction agent_down down agent.direction_map }
      else if is_valid_pos agent_left ∧ agent.find_contradiction agent_left ∧ agent.get_visited agent_left == unknown then
        { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
          state_map := agent.set_visited agent_left (agent.env.get_state agent_left) agent.state_map,
          direction_map := agent.set_direction agent_left left agent.direction_map }
      else if is_valid_pos agent_right ∧ agent.find_contradiction agent_right ∧ agent.get_visited agent_right == unknown then
        { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
          state_map := agent.set_visited agent_right (agent.env.get_state agent_right) agent.state_map,
          direction_map := agent.set_direction agent_right right agent.direction_map }
      else
        -- return to the previous position
        match agent.get_direction agent.pos with
        | up => { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                  state_map := agent.state_map, direction_map := agent.direction_map }
        | down => { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                    state_map := agent.state_map, direction_map := agent.direction_map }
        | left => { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                    state_map := agent.state_map, direction_map := agent.direction_map }
        | right => { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                     state_map := agent.state_map, direction_map := agent.direction_map }
  | stench_breeze =>
    let pit_pos := agent.get_pit agent.pos
    let wumpus_pos := agent.get_wumpus agent.pos
    let first_stench :=
      if agent.first_stench == { x := 0, y := 0 } then
        agent.pos
      else
        agent.first_stench
    if ¬ wumpus_pos == agent.pos then
      -- shot the wumpus
      if agent.pos.x < wumpus_pos.x ∧ agent.shot right then
        { direction := right, pos := agent_right, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_right right agent.direction_map }
      else if agent.pos.x > wumpus_pos.x ∧ agent.shot left then
        { direction := left, pos := agent_left, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_left left agent.direction_map }
      else if agent.pos.y < wumpus_pos.y ∧ agent.shot down then
        { direction := down, pos := agent_down, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_down down agent.direction_map }
      else -- agent.pos.y > wumpus_pos.y ∧ agent.shot up
        { direction := up, pos := agent_up, is_shot := true, first_stench := first_stench,
          env := {map := agent.env.set_shot_env wumpus_pos agent.env.map},
          state_map := agent.set_shot_state_map wumpus_pos agent.state_map,
          direction_map := agent.set_direction agent_up up agent.direction_map }
    else if ¬ pit_pos == agent.pos then
      -- return to the previous position and set the pit as visited
      match agent.get_direction agent.pos with
        | up => { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                  state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
        | down => { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                    state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
        | left => { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                    state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
        | right => { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                     state_map := agent.set_visited pit_pos pit agent.state_map, direction_map := agent.direction_map }
    else
      -- return to the previous position
      match agent.get_direction agent.pos with
        | up => { direction := down, pos := agent_down, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                  state_map := agent.state_map, direction_map := agent.direction_map }
        | down => { direction := up, pos := agent_up, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                    state_map := agent.state_map, direction_map := agent.direction_map }
        | left => { direction := right, pos := agent_right, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                    state_map := agent.state_map, direction_map := agent.direction_map }
        | right => { direction := left, pos := agent_left, is_shot := agent.is_shot, first_stench := first_stench, env := agent.env,
                     state_map := agent.state_map, direction_map := agent.direction_map }
  | _ => agent

def multi_step (agent : Agent) (steps : Nat) : Agent :=
  if steps <= 1 then
    step agent
  else
    multi_step (step agent) (steps - 1)

#eval (multi_step init_agent 1).pos
#eval (multi_step init_agent 2).pos
#eval (multi_step init_agent 3).pos
#eval (multi_step init_agent 4).pos
#eval (multi_step init_agent 5).pos
#eval (multi_step init_agent 6).pos
#eval (multi_step init_agent 7).pos
#eval (multi_step init_agent 8).pos
#eval (multi_step init_agent 9).pos
#eval (multi_step init_agent 10).pos
#eval (multi_step init_agent 11).pos
#eval (multi_step init_agent 12).pos
#eval (multi_step init_agent 13).pos
#eval (multi_step init_agent 14).pos
#eval (multi_step init_agent 15).pos
#eval (multi_step init_agent 16).pos
#eval (multi_step init_agent 17).pos
#eval (multi_step init_agent 18).pos
#eval (multi_step init_agent 19).pos  -- end

def test : Pos :=
  let agent := multi_step init_agent 13
  agent.get_pit agent.pos

#eval test

-- prove for safty
axiom wumpus_stench : ∀ (p : Pos) (env : Environment), is_valid_pos p → (env.get_state p == wumpus) →
  (∀ (q : Pos), Pos.adjacent p q → (env.get_state q == stench))

axiom pit_breeze : ∀ (p : Pos) (env : Environment), is_valid_pos p → (env.get_state p == pit) →
  (∀ (q : Pos), Pos.adjacent p q → (env.get_state q == breeze))

axiom one_wumpus : ∀ (env : Environment) (p q : Pos), is_valid_pos p → is_valid_pos q →
  (env.get_state p == wumpus) → (env.get_state q == wumpus) → (p = q)

axiom valid_pos : ∀ (agent : Agent), is_valid_pos agent.pos

-- set_option maxHeartbeats 1000000

def is_safe (agent : Agent) : Bool :=
    match agent.env.map[agent.pos.y]? with
    | none => false
    | some row =>
      match row[agent.pos.x]? with
      | none => false
      | some state =>
        match state with
        | pit => false
        | wumpus => false
        | pit_stench => false
        | wumpus_breeze => false
        | unknown => false
        | _ => true

theorem safe_step : ∀ (agent : Agent), is_safe agent → is_safe (step agent) := by
  intro agent
  unfold is_safe at *
  cases agent.env.map[agent.pos.y]? with
  | none =>
    simp
  | some row =>
    simp
    cases row[agent.pos.x]? with
    | none =>
      simp
    | some state =>
      simp
      cases state with
      | pit =>
        simp
      | wumpus =>
        simp
      | pit_stench =>
        simp
      | wumpus_breeze =>
        simp
      | unknown =>
        simp
      | safe =>
        simp
        -- unfold step
        -- cases agent.env.get_state agent.pos with
        -- | safe =>
        --   simp
        --   cases is_valid_pos (agent.pos.move up) with
        --   | true =>
        --     simp
        --     cases agent.get_visited (agent.pos.move up) == unknown with
        --     | true =>
        --       simp
        sorry
      | breeze =>
        simp
        sorry
      | stench =>
        simp
        sorry
      | stench_breeze =>
        simp
        sorry
