
method minSubArray(numArray : seq<int>, minSum : int) returns (minFound : int)
  requires |numArray| >= 1
  requires forall k :: 0 <= k < |numArray| ==> numArray[k] > 0
  ensures forall k :: 0 <= k < |numArray| - 1 ==> forall j :: 1 < j < minFound ==> sumArray(numArray, k, j) < minSum
  {
    var start : int := 0;
    var end : int := 0;
    var sum : int := numArray[0];
    minFound := |numArray|;
    
    while(end < |numArray|) 
      decreases |numArray| - end 
    {
      while (sum < minSum && end < |numArray|) {
        sum := sum + numArray[end];
        end := end + 1;
      }
      
      while(sum > minSum && start < |numArray|) {
        if end - start < minFound  {
          minFound := end - start;
        }
        
        sum := sum - numArray[start];
        start := start + 1;
      }
    }   
  }


function sumArray (numArray : seq<int>, start : int, size : int) : int
  requires start >= 0
  decreases |numArray| - start
{
  if size > 0 && start < |numArray|
  then sumArray(numArray, start + 1, size - 1) + numArray[start]
  else 0
}
