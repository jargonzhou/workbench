package example.core

import gigahorse._, support.okhttp.Gigahorse
import scala.concurrent._, duration._
import play.api.libs.json._

// https://publicapi.dev/category/weather
// The National Weather Service (NWS) API: https://www.weather.gov/documentation/services-web-api

object Weather {
  lazy val http = Gigahorse.http(Gigahorse.config)

  def weather: Future[String] = {
    // val baseUrl = "https://www.metaweather.com/api/location"
    // val locUrl = baseUrl + "/search/"
    // val weatherUrl = baseUrl + "/%s/"
    // val rLoc = Gigahorse.url(locUrl).get.
    //   addQueryString("query" -> "New York")
    val baseUrl = "https://api.weather.gov/"
    import ExecutionContext.Implicits.global
    for {
      //   loc <- http.run(rLoc, parse)
      //   woeid = (loc \ 0  \ "woeid").get
      //   rWeather = Gigahorse.url(weatherUrl format woeid).get
      weather <- http.run( Gigahorse.url(baseUrl).get, parse)
    } yield (weather \\ "status")(0).as[String].toLowerCase
  }

  private def parse = Gigahorse.asString andThen Json.parse
}