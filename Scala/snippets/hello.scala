// Scala 2.13
// def main(args: Array[String]) = {
  println("Hello, Scala!")
  for (arg <- args) {
    println(arg)
  }
// }

// Scala 3
// @main def m(args: String*) =
//   println("Hello, Scala!")
//   var i = 0
//   while i < args.length do
//     println(args(i))
//     i += 1