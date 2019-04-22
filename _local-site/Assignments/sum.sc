var l = List(2, 3, 5, 9)
var sum = 0

while (l.nonEmpty) {
  sum = sum + l.head
  l = l.tail
}

println(sum)

def sum0(lst: List[Int]) : Int = {
  var l = lst
  var sum = 0

  while (l.nonEmpty) {
    sum = sum + l.head
    l = l.tail
  }
  return sum
}

println(sum0(List(2, 3, 5, 9)))

def sum1(lst: List[Int]) : Int =
  if (lst.isEmpty) 0 else lst.head + sum1(lst.tail)

println(sum1(List(2, 3, 5, 9)))

val sum2 : List[Int] => Int = {
  case List() => 0
  case head :: tail => head + sum2(tail)
}

println(sum2(List(2, 3, 5, 9)))

@annotation.tailrec
def sum3(lst: List[Int], accum: Int = 0): Int =
  if (lst.isEmpty) accum else sum3(lst.tail, accum + lst.head)

println(sum3(List(2, 3, 5, 9)))
