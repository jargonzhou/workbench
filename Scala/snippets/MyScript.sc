// print banner
println("Hello World!!")

// common imports
import sys.process._
import collection.mutable

// common initialization code
val x = 123
println("x is " + 123)

def hello(): Unit = {
  println("Hello Scala!")
}


// import $ivy.`com.lihaoyi::os-lib:0.11.3`

//
// run in current folder
//
def exec(commands: String*): Unit = 
  val res = os.proc(commands).call()
  if res.exitCode == 0 then
    print(res.out.trim())
  else
    print(res.err.trim())

def execForce(commands: String*): Unit =
  try
    exec(commands*)
  catch
    case ex: Exception => println(ex)


//
// run in specific folder
//

def exec2(cwd: os.Path = os.pwd, commands: String*): Unit = 
  val res = os.proc(commands).call(cwd=cwd)
  if res.exitCode == 0 then
    print(res.out.trim())
  else
    print(res.err.trim())

def execForce2(cwd: os.Path = os.pwd, commands: String*): Unit =
  try
    exec2(cwd=cwd, commands*)
  catch
    case ex: Exception => println(ex)

// Examples:
// exec2(cwd=os.pwd / "hello-world", "sbt.bat", "run")
// exec2(commands=Seq[String]("sbt.bat", "--version") : _*)