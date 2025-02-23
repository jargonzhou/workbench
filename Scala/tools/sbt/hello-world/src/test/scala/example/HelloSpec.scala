package example

import org.scalatest.funsuite.AsyncFunSuite

class HelloSpec extends AsyncFunSuite {
  test("Hello should start with H") {
    // Hello, as opposed to hello
    assert("Hello".startsWith("H"))
  }
}
