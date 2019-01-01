def sum1(l: List[Int]) : Int = {
  var tot = 0
  var lst = l
  while (lst.nonEmpty) {
    tot += lst.head
    lst = lst.tail
  }
  return tot
}

println(sum1(List(2, 3, 7, 9)))

def sum2(l: List[Int]) : Int = l match {
  case List() => 0
  case head :: tail => head + sum2(tail)
}

println(sum2(List(2, 3, 7, 9)))

val sum3 : List[Int] => Int = {
  case List() => 0
  case head :: tail => head + sum2(tail)
}

println(sum3(List(2, 3, 7, 9)))

@annotation.tailrec
def sum4(l: List[Int], accum: Int = 0) : Int = l match {
  case List() => accum
  case head :: tail => sum4(tail, accum + head)
}

println(sum4(List(2, 3, 7, 9)))
