package enumeration

import scala.annotation.tailrec
import scala.collection.Searching.{Found, InsertionPoint, SearchResult}
import scala.collection.mutable.ArrayBuffer

class SearchUtils {
  def searchBy[A,B](list: ArrayBuffer[A], elem: A, f: A => B)(implicit ord: Ordering[B]): SearchResult =
    binarySearch(list, elem, 0, list.length,f)(ord)
  @tailrec
  private def binarySearch[A,B](list: ArrayBuffer[A], elem: A, from: Int, to: Int, f: A => B)
                               (implicit ord: Ordering[B]): SearchResult = {
    if (to == from) InsertionPoint(from) else {
      val idx = from+(to-from-1)/2
      math.signum(ord.compare(f(elem), f(list(idx)))) match {
        case -1 => binarySearch(list, elem, from, idx, f)(ord)
        case  1 => binarySearch(list, elem, idx + 1, to, f)(ord)
        case  _ => Found(idx)
      }
    }
  }
}
