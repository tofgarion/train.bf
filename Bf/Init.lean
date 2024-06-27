import Zen.Train



/-! # Basic helpers -/


/-! ## `Array` extensions

Adding a few features to Lean's `Array`.
-/
namespace Array

variable (array : Array α) (h : array.size ≠ 0 := by omega)

/-- Last element of a non-empty array. -/
def last : α := array[array.size - 1]

/-- Pops a non-empty array to yield the last element and the popped array. -/
def pop' : α × Array α := (array.last, array.pop)

end Array



/-! ## Helpers specific to this project -/
namespace Zen.Train.Bf

def asciiToChar (n : Nat) : Char :=
  match n with
  | 32 => ' '   | 48 => '0'   | 64 => '@'   | 80 => 'P'  |  96 => '`'  | 112 => 'p'
  | 33 => '!'   | 49 => '1'   | 65 => 'A'   | 81 => 'Q'  |  97 => 'a'  | 113 => 'q'
  | 34 => '"'   | 50 => '2'   | 66 => 'B'   | 82 => 'R'  |  98 => 'b'  | 114 => 'r'
  | 35 => '#'   | 51 => '3'   | 67 => 'C'   | 83 => 'S'  |  99 => 'c'  | 115 => 's'
  | 36 => '$'   | 52 => '4'   | 68 => 'D'   | 84 => 'T'  | 100 => 'd'  | 116 => 't'
  | 37 => '%'   | 53 => '5'   | 69 => 'E'   | 85 => 'U'  | 101 => 'e'  | 117 => 'u'
  | 38 => '&'   | 54 => '6'   | 70 => 'F'   | 86 => 'V'  | 102 => 'f'  | 118 => 'v'
  | 39 => '\''  | 55 => '7'   | 71 => 'G'   | 87 => 'W'  | 103 => 'g'  | 119 => 'w'
  | 40 => '('   | 56 => '8'   | 72 => 'H'   | 88 => 'X'  | 104 => 'h'  | 120 => 'x'
  | 41 => ')'   | 57 => '9'   | 73 => 'I'   | 89 => 'Y'  | 105 => 'i'  | 121 => 'y'
  | 42 => '*'   | 58 => ':'   | 74 => 'J'   | 90 => 'Z'  | 106 => 'j'  | 122 => 'z'
  | 43 => '+'   | 59 => ';'   | 75 => 'K'   | 91 => '['  | 107 => 'k'  | 123 => '{'
  | 44 => ','   | 60 => '<'   | 76 => 'L'   | 92 => '\\' | 108 => 'l'  | 124 => '|'
  | 45 => '-'   | 61 => '='   | 77 => 'M'   | 93 => ']'  | 109 => 'm'  | 125 => '}'
  | 46 => '.'   | 62 => '>'   | 78 => 'N'   | 94 => '^'  | 110 => 'n'  | 126 => '~'
  | 47 => '/'   | 63 => '?'   | 79 => 'O'   | 95 => '_'  | 111 => 'o'
  | _ => '¿'


/-- Same as `#check`, but does not produce *info* output.

Errors and warnings are still visible though. -/
syntax "#checkout" term : command

macro_rules
| `(#checkout $t) => `(#guard_msgs(drop info) in #check $t)

#checkout List
