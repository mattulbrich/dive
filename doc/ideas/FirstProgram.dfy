
d minSubArray(numArray : array<int>, minSum : int) returns (minSize : int)
  requires numArray.Length >= 1
  requires forall k :: 0 <= k < numArray.Length ==> numArray[k] > 0
  ensures forall k :: 0 <= k < numArray.Length - 1 ==> forall j :: 1 < j < minSize ==> sumArray(numArray, k, j) < minSum
  {
    var start : int := 0;
    var end : int := 0;
    var sum : int := numArray[0];
    var minFound : int := numArray.Length;
    
    while(end < numArray.Length) 
      decreases numArray.Length - end 
    {
      while (sum < minSum && end < numArray.Length) {
        sum := sum + numArray[end];
        end := end + 1;
      }
      
      while(sum > minSum && start < numArray.Length) {
        if end - start < minFound  {
          minFound := end - start;
        }
        
        sum := sum - numArray[start];
        start := start + 1;
      }
    }  
    return minFound;  
  }


function sumArray (numArray : array<int>, start : int, size : int) : int
  requires start >= 0
  reads numArray
  decreases numArray.Length - start
{
  if size > 0 && start < numArray.Length
  then sumArray(numArray, start + 1, size - 1) + numArray[start]
  else 0
}
