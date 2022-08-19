import org.junit.* ;
import static org.junit.Assert.* ;
import java.io.*;

public class pcalTest {
	
	public String expectedOutput(String s){
	   try{
            InputStream filein;
			filein = new java.io.FileInputStream(s);
			String expectedOut = new String();
			
			StringBuffer buf = new StringBuffer();
			BufferedReader b = new BufferedReader (new InputStreamReader(filein));
			
			while(b.ready())
				buf.append(b.readLine() + "\n");
			expectedOut = buf.toString().trim();
			return expectedOut;
			
        }catch (FileNotFoundException e){
		   System.out.println("The file "+ s +" doesn't exist");
		   }
		 catch (IOException e) {
		   System.out.println("Buffer error");
			} 
		return null;		
	}
    
    @Test
    public void test_Skip() throws ParseException {
		System.out.println("\nTest Skip");    
       String in = 
    	   "algorithm Skip\n"+
    	   //"extends Sequences\n"+
    	   //"constants N\n"+
    	   "process Skip[1]\n"+
    	   "begin\n"+
    	   "    start: skip;\n"+
    	   "end process\n"+
    	   "end algorithm\n";  
    	            
       String expectedOut = expectedOutput("./test/skipExpec.tla");            
              
       String out = pcal.test(in, "./test/Skip.pcal");		

	   assertEquals(expectedOut, out);
    }
    
    @Test
    public void test_Assign() throws ParseException {
		System.out.println("\nTest Assign");    
       String in = 
    	   "algorithm Assign\n"+    	   
    	   "variables i = 0, j, k\n"+
    	   "process Assign[1]\n"+
    	   "begin\n"+
    	   "    start: j := 1;\n"+
    	   "end process\n"+
    	   "end algorithm\n";  
    	        
       String expectedOut = expectedOutput("./test/assignExpec.tla");            
              
       String out = pcal.test(in, "./test/Assign.pcal");		

	   assertEquals(expectedOut, out);
    }
    
    @Test
    public void test_Let() throws ParseException {
		System.out.println("\nTest LET");    
       String in = 
    	   "algorithm Let\n"+    	   
    	   "variables i = 0, j, k = {}\n"+
    	   "process Let[1]\n"+
    	   "begin\n"+
    	   "    start: j := 1;\n"+
    	   "           k := {2};\n"+
    	   "           with it \\in 1..1"+
    	   "               skip\n"+
    	   "           end with\n"+
    	   "end process\n"+
    	   "end algorithm\n";  
    	        
       String expectedOut = expectedOutput("./test/letExpec.tla");            
              
       String out = pcal.test(in, "./test/Let.pcal");		

	   assertEquals(expectedOut, out);
    }
    
    @Test
    public void test_Loopif() throws ParseException {
		System.out.println("\nTest Loopif");    
       String in = 
    	   "algorithm Loopif\n"+    	   
    	   "variables i = 0, j\n"+
    	   "process Loopif[1]\n"+
    	   "begin\n"+
    	   "    start: j := 4;\n"+
    	   "           loop\n"+
    	   "               l: if (i = j) then\n"+
    	   "                      break;\n"+
    	   "                  else\n"+
    	   "                      i := i+1;\n"+
    	   "               end if\n"+
    	   "           end\n"+    	   
    	   "end process\n"+
    	   "end algorithm\n";  
    	        
       String expectedOut = expectedOutput("./test/loopifExpec.tla");            
              
       String out = pcal.test(in, "./test/Loopif.pcal");		

	   assertEquals(expectedOut, out);
    }
    
    @Test
    public void test_BranchStructure() throws ParseException {    
       System.out.println("\nTest BranchStructure");
       String in = 
    	   "algorithm airport\n"+
    	   "extends Naturals\n"+
    	   "constants N\n"+
    	   "\n"+
    	   "variables doors = [d \\in Buttoms |-> \"close\"]\n"+
    	   "\n"+
    	   "process Buttoms[N]\n"+
    	   "begin\n"+
    	   "    choose: branch doors[self] = \"open\" then close: doors[self] := \"close\";\n"+   		
    	   "		    or doors[self] = \"close\" then open: doors[self] := \"open\"; \n"+
    	   "            end branch;\n"+
    	   "end process\n"+
    	   "end algorithm\n";       
       
       String expectedOut = expectedOutput("./test/airportExpec.tla");     
              
       String out = pcal.test(in, "./test/airport.pcal");		
	       
       assertEquals(expectedOut, out);
    }

    @Test
    public void test_Definitions() throws ParseException {    
       System.out.println("\nTest Definitions");
       String in = 
    	   "algorithm Definitions\n"+
    	   "extends Naturals\n"+
    	   "\n"+
    	   "variables\n"+
    	   "    Set = {1,2,3,4,5},\n"+
    	   "    i = 0,\n"+
    	   "    l = 5,\n"+
    	   "    network = [from \\in Definitions |-> [to \\in Definitions |-> << >> ]]\n"+
    	   "\n"+
    	   "definition Foo(I) == I + 4\n"+
    	   "\n"+
    	   "definition send(from, to, msg) ==\n"+
    	   "[network EXCEPT ![from] = [@ EXCEPT ![to] = Append(@, msg)]]\n"+
    	   "\n"+
    	   "definition lol == 8\n"+    	   
    	   "\n"+
    	   "process Definitions[1]\n"+
    	   "\n"+
    	   "definition pas == 225\n"+    	   
    	   "\n"+
    	   "begin\n"+
    	   "    start: i := l + lol;\n"+
    	   "           i := i + Foo(l) + pas;\n"+
    	   "           network := send(1,2,456);"+
    	   "end process\n"+
    	   "end algorithm\n";                               	       	
       
       String expectedOut = expectedOutput("./test/definitionsExpec.tla");     
              
       String out = pcal.test(in, "./test/Definitions.pcal");		
	   
       assertEquals(expectedOut, out);

    }
    
    @Test
    public void test_LetNro2() throws ParseException {    
       System.out.println("\nTest Let number 2");
       String in = 
    	   "algorithm LetNro2\n"+
    	   "extends Naturals\n"+
    	   "\n"+
    	   "variables\n"+    	   
    	   "    i = 0\n"+    	   
    	   "\n"+
    	   "definition foo(k) ==\n"+
    	   "  LET x == 4\n"+
    	   "      y == 3\n"+
    	   "  IN x + k + y\n"+
    	   "\n"+
    	   "definition goo ==\n"+
    	   "  LET x == 7\n"+
    	   "  IN x \n"+
    	   "\n"+
    	   "process LetNro2[1]\n"+
    	   "\n"+
    	   "begin\n"+
    	   "    start: i := i + foo(5);\n"+
    	   "end process\n"+
    	   "end algorithm\n";                               	       	
       
       String expectedOut = expectedOutput("./test/LetNro2Expec.tla");     
              
       String out = pcal.test(in, "./test/LetNro2.pcal");		
	   
       assertEquals(expectedOut, out);       
    }
    
    @Test
    public void test_setComprehension() throws ParseException {    
       System.out.println("\nTest setComprehension");
       String in = 
    	   "algorithm setComprehension\n"+
    	   "extends Naturals\n"+
    	   "\n"+
    	   "variables\n"+    	   
    	   "    i = {},j\n"+    	   
    	   "\n"+
    	   "process setComprehension[2]\n"+
    	   "\n"+
    	   "begin\n"+
    	   "    start: i := {x \\in Nat : x + y > 2};\n"+
    	   "           j := {n+2 : n \\in 1..10};\n"+
    	   "end process\n"+
    	   "end algorithm\n";                               	       	
       
       String expectedOut = expectedOutput("./test/setComprehensionExpec.tla");     
              
       String out = pcal.test(in, "./test/setComprehension.pcal");		
	   
       assertEquals(expectedOut, out);
    }
    
    @Test
    public void test_nestedFor() throws ParseException {    
       System.out.println("\nTest nestedFor");
       String in = 
    	   "algorithm For\n"+
    	   "extends Naturals,TLC\n"+
    	   "\n"+
    	   "variables u, i\n"+    	       	   
    	   "\n"+
    	   "process For[2]\n"+
    	   "\n"+
    	   "begin\n"+
    	   "    start: for i \\in 1..4\n"+
    	   "               for u \\in 1..3\n"+
    	   "                   print(i);\n"+
    	   "                end for\n"+
    	   "           end for\n"+
    	   "end process\n"+
    	   "end algorithm\n";                               	       	
       
       String expectedOut = expectedOutput("./test/nestedForExpec.tla");     
              
       String out = pcal.test(in, "./test/nestedFor.pcal");		
	   
       assertEquals(expectedOut, out);
    }
    
    @Test
    public void test_With() throws ParseException {    
       System.out.println("\nTest With");
       String in = 
    	   "algorithm With\n"+
    	   "extends Naturals\n"+
    	   "\n"+
    	   "variables j, i\n"+    	       	   
    	   "\n"+
    	   "process With[1]\n"+
    	   "\n"+
    	   "begin\n"+
    	   "    l1: with i \\in 1..4\n"+
    	   "             j := i*3;\n"+
    	   "    l2:      j := j+i;\n"+
    	   "        end with\n"+
    	   "end process\n"+
    	   "end algorithm\n";                               	       	
       
       String expectedOut = expectedOutput("./test/withExpec.tla");     
              
       String out = pcal.test(in, "./test/With.pcal");		
	   
       assertEquals(expectedOut, out);       
    }
    
    @Test
    public void test_Branch() throws ParseException {    
       System.out.println("\nTest Branch");
       String in = 
    	   "algorithm Branch\n"+
    	   "extends Naturals\n"+
    	   "\n"+
    	   "variables k, i\n"+    	       	   
    	   "\n"+
    	   "process Branch[1]\n"+
    	   "\n"+
    	   "begin\n"+
    	   "    branch i > 0 then\n"+
    	   "           i := 3;\n"+
    	   "    or i < 4 then\n"+
    	   "        i := 5\n"+
    	   "    end branch;\n"+
    	   "    k := 6\n"+
    	   "end process\n"+
    	   "end algorithm\n";                              	       	
       
       String expectedOut = expectedOutput("./test/branchExpec.tla");     
              
       String out = pcal.test(in, "./test/branch.pcal");		
	   
       assertEquals(expectedOut, out);       
    }
    
    @Test
    public void test_atomic() throws ParseException {    
       System.out.println("\nTest Atomic");
       String in = 
    	   "algorithm Atomic\n"+
    	   "extends Naturals\n"+
    	   "\n"+
    	   "variables k, i\n"+    	       	   
    	   "\n"+
    	   "process Atomic[1]\n"+
    	   "\n"+
    	   "begin\n"+
    	   "    atomic\n"+
    	   "          l1: i := 5;\n"+
    	   "          l2: i:= 6;\n"+
    	   "    end atomic;\n"+
    	   "end process\n"+
    	   "end algorithm\n";                               	       	
       
       String expectedOut = expectedOutput("./test/atomicExpec.tla");     
              
       String out = pcal.test(in, "./test/atomic.pcal");		
	   
       assertEquals(expectedOut, out);
       	
    }
    
    @Test
    public void test_LamportMutex() throws ParseException {    
       System.out.println("\nTest LamportMutex");
       System.out.println("(takes some time to be compile)");
                    
       String in = expectedOutput("./test/LamportMutex.pcal");
       String expectedOut = expectedOutput("./test/LamportMutexExpec.tla");
       
       String out = pcal.test(in, "./test/LamportMutex.pcal");		
       assertEquals(expectedOut, out);
       assertTrue(true);
    } 
    
}
