import java.io.*;


interface PcalTLAGeneratorInterface {
	void start(ExplodedTree tree, OutputStream out, String fileName);
}

public class PcalTLAGenerator implements PcalTLAGeneratorInterface{
    OutputStream outputStream;
    PrintStream printStream;
    String SpecName;

    public PcalTLAGenerator() 
    {
        SpecName = "Spec";
    }
    
    public void start(ExplodedTree tree, OutputStream out, String fileName)
    {
    	outputStream = out;
    	String shortFileName = "";    	
    	fileName=fileName.substring(0,fileName.lastIndexOf("."));
        if(fileName.contains("/"))
        {
            shortFileName=fileName.substring(fileName.lastIndexOf("/")+1, fileName.length());
        }
        else
        {
            shortFileName = fileName;
        }
        try
        {   
            out.write(("------------------------------ MODULE " + shortFileName + " ---------------------------\n\n").getBytes());
            
        	outputStream = new FileOutputStream(fileName + ".tla");
            printStream = new PrintStream( outputStream );
            printStream.println("------------------------------ MODULE " + shortFileName + " ---------------------------\n");
			generateTLA(tree, out);
            printStream.println("=================================================================================");
            printStream.close();
            
            out.write(("\n=================================================================================").getBytes());
            out.close();
            System.out.println(fileName + ".tla created.");
            
        }
        catch (Exception e)
        {
                System.err.println ("Error writing to TLA file: " + e.getMessage());
        }            
        createConfigFile(fileName, tree);
        System.out.println(fileName + ".cfg created.");
        
    }
    
    private void generateTLA(ExplodedTree tree, OutputStream out)
    {
        String headerInfo = tree.getHeaderInformation();
        printStream.println(headerInfo+"\n");
        
        String list = tree.getVariableList();
        printStream.println(list);
        printStream.println("\nPush(s,e) == e \\circ s " + "\n");
        
        try{ out.write((headerInfo+"\n").getBytes());
        	 out.write(("\n").getBytes());	
        	 out.write(list.getBytes());
        	 out.write(("\n").getBytes());
        	 out.write(("\nPush(s,e) == e \\circ s " + "\n").getBytes());
        	 out.write(("\n").getBytes());
        } catch (IOException e){
        	  System.out.println("Cannot create out string");
        }
        
        list = "";//tree.generateIndepMatrix();
        list += tree.getLabelDescrption();
        printStream.println(list);
        try{ out.write(list.getBytes());
        } catch (IOException e){
        	System.out.println("Cannot create out string");
        	}
        String fairness = "";
        fairness = tree.getFairnessDescription();
        if(fairness.compareTo("") != 0)
        {
            printStream.println(fairness);
            SpecName = "FairSpec";
            printStream.println("FairSpec == Spec /\\ Fairness");
            
            try{ out.write(fairness.getBytes());
            	 out.write(("FairSpec == Spec /\\ Fairness").getBytes());	
            } catch (IOException e){
            	System.out.println("Cannot create out string");
              }
        }                
        
        String property = "";
        property = tree.getPropertyDescription();
        if(property.compareTo("") != 0)
        {
            printStream.println(property);
          
            try{ out.write(fairness.getBytes());
       	 	     out.write(("FairSpec == Spec /\\ Fairness").getBytes());	
            } catch (IOException e){
            		System.out.println("Cannot create out string");
              }
        }
    }
    private void createConfigFile(String fileName, ExplodedTree tree)
    {
        try
        {
            FileOutputStream cfgOUT;
            PrintStream cfgPRINT;
            cfgOUT = new FileOutputStream(fileName + ".cfg");
            cfgPRINT = new PrintStream( cfgOUT );
            cfgPRINT.println("SPECIFICATION " + SpecName);
            int numOfTemporalProperties = tree.getNumOfProperties("temporal");
            int numOfInvariantProperties = tree.getNumOfProperties("invariant");
            int numOfConstraints = tree.getNumOfProperties("constraint");
            
            if(numOfTemporalProperties > 0)
            {
                cfgPRINT.println("PROPERTY  Temp0");
                for(int i=1;i<numOfTemporalProperties;i++)
                {
                    cfgPRINT.println("\t  Temp"+i);
                }
            }
            if(numOfInvariantProperties > 0)
            {
                cfgPRINT.println("INVARIANT  Inv0");
                for(int i=1;i<numOfInvariantProperties;i++)
                {
                    cfgPRINT.println("\t   Inv"+i);
                }
            }
            if(numOfConstraints > 0)
            {
                cfgPRINT.println("CONSTRAINT  Const0");
                for(int i=1;i<numOfConstraints;i++)
                {
                    cfgPRINT.println("\t   Const"+i);
                }
            }
            
            
            String constantDefInfo = tree.getConstantDefInfo();
            cfgPRINT.println("\nCONSTANTS  any = 99");
            if(!constantDefInfo.equals(""))
            {
                cfgPRINT.println("\n"+constantDefInfo);
            }
            cfgPRINT.println("\n\\* Add statements after this line.");
            cfgPRINT.close();
        }
        catch (Exception e)
        {
                System.err.println ("Error writing to configuration file :" + e.getMessage());
        }            
    
    }
}
