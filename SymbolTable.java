/* Symbol Table Class */
import java.util.*;

interface SymbolTableInterface
{
    String addSymbol(String name, String type, String defaultValue);// Adds new frames in case of processes, procedures, definitions, and algorithm
    String checkDeclaration(String name, String type, int noofparameters, String location);
    String checkExistenceAddMethod(String name, String type, String location);
    void updateConstantInitialization(String symbol);
    void popLastFrame();
    void showWarnings();
    
    String[] getScopeInformation(String symbol, String type, int noOfParameters);
    void copyCurrentProcessNames(ArrayList<String> list);
	void setProcessParentRelationship(String processName, String parentName);
	String getParentName(String processName);
	boolean confirmDeclaration(String processName, String variableName);	//Confirms the declaration of a variable in the given process
	
}
public class SymbolTable implements SymbolTableInterface
{
    private ArrayList<Frame> frameStack;
    private final int VARIABLE = 1;
    private final int FUNCTION = 2;
    private final int PROCESS = 3;
    private final int THREAD = 4;
    private final int PROCEDURE = 5;
    private final int CONSTANT = 6;
    private final int PARAMETER = 7;
    private final int ALGORITHM = 8;
    private final int DEFINITION = 9;
    private Map<String, String> warnings;
    private ArrayList<String> tempConstantInitList;
    private ArrayList<String> labelNameList;
    private ArrayList<String> auxVariables;
	private ArrayList<String> keywords = new ArrayList<>(Arrays.asList("Len", "Tail", "Append", "Head", "lowerbound", "upperbound", "TRUE", "FALSE", "Main"));

	/*SA: Added on 13-7-2017 to have complete hierarchy required for the translation of properties
		Maintains process name along with parent process's name in the list ASSUMING that the process names are not repeated in the algorithm.
		*/
    private Map<String, String> processParentRelationList = new LinkedHashMap<String, String>();
    private ArrayList<Frame> removedFrames;
	


    /**
     * This class maintains all the information regarding a particular scope.
     * frameStack is a list of the objects of this class called Frames.
     */
    private class Frame{
        private String name;
        private String originalName;
        private int type;
        Map map;
        private int numberOfParameters;
        private ArrayList<String> processNames;
        
        /**
         * This class allows to maintains information regarding method name and
         * its number of parameters. A method can be a function/thread/process/
         * procedure.
         */
        private class MethodDeclaration{
            private String methodName;
            private int noOfParameters;
            private String labelName;
            Map map;
            public MethodDeclaration(String n, int np){
                methodName = n;
                noOfParameters = np;
                labelName = "";
                map = new LinkedHashMap();
            }
            /**
             * This function is an interface for method declaration record to 
             * read the name of a method
             * @return It returns the name of a method.
             */
            public String getName(){
                return methodName;
            }
            /**
             * This function is an interface for method declaration record to 
             * read the number of parameters.
             * @return It returns the number of parameters.
             */
            public int getNoOfParameters(){
                return noOfParameters;
            }
            /**
             * It updates the list of declarations.
             * @param m It is the list of variables, functions...
             */
            public void setDeclarations(Map m)
            {
                map.putAll(m);
            }
            /**
             * It sets the corresponding starting label for the method.
             * @param name It is the label name.
             */
            public void setLabelName(String name)
            {
                labelName = name;
            }
            /**
             * It returns the label name.
             * @return Label 
             */
            public String getLabelName()
            {
                return labelName;
            }
        }
        public Frame() {   
            name = "";
            originalName = "";
            type = 0;
            numberOfParameters = 0;
            map = new LinkedHashMap();
            processNames = new ArrayList<String>();
        }  
        /**
         * It updates the label information.
         * @param symbolName    It is the name of method.
         * @param type          It is type e.g., function/thread...
         * @param nop           It is number of parameters.
         * @param name          It is label name.
         */
        public void setLabelInformation(String symbolName, int type, int nop, String name)
        {
            String key = getSymbolwithPrefixandPostfix(symbolName, type, nop);
            MethodDeclaration md = (MethodDeclaration)map.get(key);
            md.setLabelName(name);
        }
        /**
         * It retrieves the label information.
         * @param symbolName    It is the name of method.
         * @param type          It is type e.g., function/thread...
         * @param nop           It is number of parameters.
         * @return
         */
        public String getLabelInformation(String symbolName, int type, int nop)
        {
            String key = getSymbolwithPrefixandPostfix(symbolName, type, nop);
            MethodDeclaration md = (MethodDeclaration)map.get(key);
            if(md ==null && type == PROCESS)
            {
                key = getSymbolwithPrefixandPostfix(symbolName, THREAD, nop);
                md = (MethodDeclaration)map.get(key);
            }
            else if(md ==null && type == FUNCTION)
            {
                key = getSymbolwithPrefixandPostfix(symbolName, PROCEDURE, nop);
                md = (MethodDeclaration)map.get(key);
            }
            return md.getLabelName();
        }
        /**
         * It updates the list of declarations.
         * @param symbolName    It is the name of method.
         * @param type          It is type e.g., function/thread...
         * @param nop           It is number of parameters.
         * @param m             It is the list of variables/functions...
         */
        public void setDeclarations(String symbolName, int type, int nop, Map m)
        {
            String key = getSymbolwithPrefixandPostfix(symbolName, type, nop);
            MethodDeclaration md = (MethodDeclaration)map.get(key);
            md.setDeclarations(m);
        }
        /**
         * It retrieves the list of variables for the corresponding method.
         * @param symbolName    It is the name of method.
         * @param type          It is type e.g., function/thread...
         * @param nop           It is number of parameters.
         * @return
         */
        public Map getVarDeclarations(String symbolName, int type, int nop)
        {            
            String key = getSymbolwithPrefixandPostfix(symbolName, type, nop);
            MethodDeclaration md = (MethodDeclaration)map.get(key);
            if(md == null && type == PROCESS)
            {
                key = getSymbolwithPrefixandPostfix(symbolName, THREAD, nop);
                md = (MethodDeclaration)map.get(key);
            }
            else if(md == null && type == FUNCTION)
            {
                key = getSymbolwithPrefixandPostfix(symbolName, PROCEDURE, nop);
                md = (MethodDeclaration)map.get(key);
            }
            Map list = new LinkedHashMap();
            try
            {
                Iterator iter = (md.map).entrySet().iterator(); 
                for (iter = (md.map).entrySet().iterator(); iter.hasNext();)
                { 
                    Map.Entry entry = (Map.Entry)iter.next();
                    String key1 = (String)entry.getKey();
                    String prefix = key1.substring(0, 4);
                    if(prefix.compareTo("_var") == 0 || prefix.compareTo("var_") == 0 || prefix.compareTo("cnt_") == 0)
                    {
                        String name = "";
                        if(prefix.compareTo("_var") == 0)
                        {//To include the variables that were defined in with or for statement with limited scope (they were deleted using an "_" infront of there id)
                            name = key1.substring(5, key1.length());
                        }
                        else
                        {
                            name = key1.substring(4, key1.length());
                        }
                        String value = (String)entry.getValue();
                        list.put(name, value);
                    }
                }
            }
            catch(Exception e)
            {
                throwExceptionAndExit(e);
            }
            return list;
        }
        /**
         * It sets the name and type of the frame. e.g., function and function name..
         * @param n     It is the name of the method.
         * @param t     It is the type of the method.
         */
        public void setNameAndType(String n, int t) {
            name = n;
            type = t;
        }
        /**
         * This functions takes original name of the process/procedure.
         * A name that doesn't contain any reference to its parents.
         * @param n
         */
        public void setOriginalName(String n){
            originalName = n;
        }
        /**
         * This is an interface function to read the name of the frame.
         * @return It returns the name of function/thread/procedure/process.
         */
        public String getName(){
            return name;
        }
        /**
         * This function returns the original name of the process/procedure/definition
         * A name that doesn't contain any reference to its parents.
         * @return
         */
        public String getOriginalName(){
            return originalName;
        }
        /**
         * This function returns the type of the frame whether it is
         * process, thread, function...
         * @return It returns a number for corresponding type.
         */
        public int getType()
        {
            return type;
        }
        /**
         * This is an interface function to read the number of parameters, if
         * it is a function/thread/process/procedure.
         * @return It returns the number of parameters.
         */
        public int getNoOfParameters(){
            return numberOfParameters;
        }
        /**
         * This function adds variable, constant, function,... in the frame. It appends prefix and postfix information
         * to the name of the symbol, e.g., It helps in adding methods of same name but with different number of parameters.
         * @param n It is the name of the symbol.
         * @param t It is the type of symbol whether its variable, function....
         * @param nop It is the number of parameters that a method takes except for variable/constant/parameter.
         * @param def_value It is the value of a variable, constant or parameter.
         */
        public void addsymbol(String n, int t, int nop, String def_value){
            String key = "";
            Object value = def_value;
            MethodDeclaration new_method;
            new_method = new MethodDeclaration(n, nop);
            key = getSymbolwithPrefixandPostfix(n, t, nop);
            switch (t)
            {
                case PARAMETER : numberOfParameters++;
                case CONSTANT : 
                case VARIABLE : value = def_value; break;
                case FUNCTION :
                case DEFINITION :
                case THREAD : 
                case PROCESS : 
                case PROCEDURE : value = new_method; break;
            }
            map.put(key, value);
        }
        public void removeSymbol(String symbol)
        {
            String key = getSymbolwithPrefixandPostfix(symbol, VARIABLE, 0);
            Object value = map.remove(key);
            key = "_" + key;
            //map.put(key, value); Commented because it was adding the auxilliary variable back to the list
			//System.out.println("To be checked: Might be need an update");
        }
        /**
         * This function looks for a symbol in a frame depending on its
         * type whether its a variable/constant/parameter/function/thread/process/
         * procedure. During parsing process, we cannot differentiate between a function and 
         * procedure, so it requires to search a symbol with type "function", using two different
         * prefix information. And same is the case with process and thread.
         * 
         * @param symbolName It is the name of the symbol.
         * @param type It is the type of symbol whether its variable, function....
         * @param nop It is the number of parameters.
         * @return It returns true if symbol is found and false, if not.
         */
        public boolean searchsymbol(String symbolName, int type, int nop){
            boolean found = false;
            String key = getSymbolwithPrefixandPostfix(symbolName, type, nop);
            
            found = search(key);
            
            if(!found && type == PROCESS)
                key = getSymbolwithPrefixandPostfix(symbolName, THREAD, nop);
            else if(!found && type == FUNCTION)
                key = getSymbolwithPrefixandPostfix(symbolName, PROCEDURE, nop);
            else if(!found && type == DEFINITION)
                key = getSymbolwithPrefixandPostfix(symbolName, DEFINITION, nop);
            else if(!found && type == VARIABLE)
            {
                key = getSymbolwithPrefixandPostfix(symbolName, CONSTANT, 0);
            }
            found = search(key);
            return found;
        }
        /**
         * It actually searches for the symbol.
         * @param key it is the name of the symbol with prefix and postfix information.
         * @return It returns true if symbol is found and false, if not.
         */
        private boolean search(String key){
            if(map.get(key) != null)
                return true;
            else
                return false;
        }
        /**
         * This function adds prefix and postfix information for the symbols. e.g.,
         * for a variable "i" it will return "var_i";
         * @param symbol    It is the name of symbol.
         * @param type      It is the type of symbol whether its variable, function....
         * @param nop       It is the number of parameters if its a method otherwise 0.
         * @return          It returns name of a symbol with prefix and postfix information.
         */
        private String getSymbolwithPrefixandPostfix(String symbol, int type, int nop){
            String withPrefix = "";
            switch (type)
            {
                    case VARIABLE : 
                    case PARAMETER : 
                        withPrefix = "var_" + symbol; break;
                    case CONSTANT : 
                        withPrefix = "cnt_" + symbol; break;
                    case FUNCTION :
                        withPrefix = "func_" + symbol + "_" + nop; break;
                    case DEFINITION :
                        withPrefix = "def_" + symbol + "_" + nop; break;
                    case PROCEDURE : 
                        withPrefix = "proced_" + symbol + "_" + nop; break;
                    case THREAD : 
                        withPrefix = "thr_" + symbol + "_" + nop; break;
                    case PROCESS : 
                        withPrefix = "process_" + symbol + "_" + nop; break;
            }
            return withPrefix;
        }
    }
    public SymbolTable() {
        frameStack = new ArrayList();
		removedFrames = new ArrayList();
        warnings = new LinkedHashMap<String, String>();
		processParentRelationList = new LinkedHashMap<String, String>();
        tempConstantInitList = new ArrayList<String>();
        labelNameList = new ArrayList<String>();
        auxVariables = new ArrayList<String>();
    }
    /**
     * This function takes the name and its type to enter the symbol information. 
     * To enter a variable/constant/parameter it checks for its existence. But for methods
     * it simply addes a new frame without entering their information in the 
     * enclosing frame. It is added after reading there parameter information.
     * @see checkexistence_and_addmethod(...)
     * @param name  It is the name of the symbol.
     * @param type  It tells us about the symbol that whether is a function, thread, process, variable or constant.
     * @param defaultValue  It is the default value of the symbol if it is variable.
     * @exception   If the symbol already exists then it throws exception.
     */
    public String addSymbol(String name, String type, String defaultValue){
    	if(type.equals("aux"))
    	{
    		auxVariables.add(name);
    		return "";
    	}
      int type_int = getType(type);
      //System.out.println("Add "+name+" (type: "+type+";typeint: "+type_int+";defaults to:"+defaultValue+") to the SymbolTable");
      if(type_int != ALGORITHM)
      {
          int currentFrameNo = frameStack.size() - 1;
          Frame curr_frame = (Frame)frameStack.get(currentFrameNo);

          if( type_int == VARIABLE || type_int == CONSTANT || type_int == PARAMETER )
          {
            if( curr_frame.searchsymbol(name, type_int, 0) == false )
            {
                for(int i = 1; i< frameStack.size();i++)
                {//Check if a process exists with the same name
                    Frame f = frameStack.get(i);
                    if(f.name.equals(name))
                    {
                        return "Symbol \"" + name + "\" already exists.";
                    }
                }
                curr_frame.addsymbol(name, type_int, 0, defaultValue);
            }
            else
            {
                return "Symbol \"" + name + "\" already exists.";
            }
          }
          else
          {
                for(int i = 1; i< frameStack.size();i++)
                {//Check if a process or a variable in parents processes exists with the same name
                    Frame f = frameStack.get(i);
                    if(f.name.equals(name))
                    {
                        return "Symbol \"" + name + "\" already exists.";
                    }
                    else if(f.searchsymbol(name, VARIABLE, 0))
                    {
                        return "Symbol \"" + name + "\" already exists.";
                    }
                }

                Frame new_frame = new Frame();
                new_frame.setNameAndType(name, type_int);
                new_frame.setOriginalName(defaultValue);
                frameStack.add(new_frame);
          }
      }
      else
      {
        Frame first_frame = new Frame();
        first_frame.setNameAndType(name, ALGORITHM);
        frameStack.add(first_frame);
      }

      return "";
    }

    public void removeAuxVariable(String symbol)
    {
    	if(auxVariables.contains(symbol))
    	{
				auxVariables.remove(symbol);
    	}
    	else
    	{
		  int currentFrameNo = frameStack.size() - 1;
		  Frame curr_frame = (Frame)frameStack.get(currentFrameNo);
		  curr_frame.removeSymbol(symbol);
    	}
    }
    /**
    * This function checks for the declaration for a given symbol.
    * 
    * @param name    It is the name of the symbol.
    * @param type    It tells us about the symbol that whether is a function, thread, process, variable or constant.
    * 
    * @warning     It show warning if the symbol is not already declared.
    */  
    public String checkDeclaration(String name, String type, int noOfParameters, String location) {
    	if(auxVariables.contains(name))
    	{
    		return "";
    	}
      int type_int = getType(type);
      int frame_no = frameStack.size() - 1;
      Frame f;
      boolean found = false;
      //check if its a name of a process at that level but not yet declared.
      f = (Frame) frameStack.get(frame_no);
      if(f.processNames.contains(name))
      {
        return "";
      }

      while(frame_no >= 0)
      {
        f = (Frame)frameStack.get(frame_no);
        found = f.searchsymbol(name, type_int, noOfParameters);
        if(found)
        {
            //return "";			//commented on 17/4/2017
			return type;
        }
        else if(type_int == VARIABLE)
        {//to check if its a definition without any parameters
            found = f.searchsymbol(name, DEFINITION, 0);
            if(found)
            {
                return "";
            }
            else
            {//Check if its a process name used to get the range of identities for the instances of that process
                found = f.searchsymbol(name, PROCESS, noOfParameters);
                if(found)
                {
                    return "";
                }
            }
        }
        frame_no--;
      }

	  if(!keywords.contains(name))	// To ignore warning for the definitions included in the extended files
	  {
	      if(type_int == FUNCTION || type_int == DEFINITION || type_int == PROCEDURE || type_int == PROCESS || type_int == THREAD)
	      {
	          warnings.put("Warning: Method \"" + name + "\" is not declared (" + location + ").\n", "");
	      }
	      else
	      {
	          warnings.put("Warning: Symbol \"" + name + "\" is not declared (" + location + ").\n", "");
	      }
	  }

      return "notfound";
    }
    public void updateConstantInitialization(String symbol)
    {
        try
        {
            if(!tempConstantInitList.contains(symbol))
            {
                tempConstantInitList.add(symbol);
            }
            else
            {
                throw new Exception("Constant \"" + symbol + "\" is already initialized.");
            }
        }
        catch(Exception e)
        {
            throwExceptionAndExit(e);
        }
    }
    /**
     * This function is called when the parser reads the declaration of a method.
     * Declaration of a method includes its name and its parameters. The information
     * about the method is stored in a new frame, but its not yet added to the enclosing
     * frame. So, over here if this method is not redeclared then it adds its information
     * in the enclosing frame.
     * @param name It is the name of the method.
     * @param type It is the type of the method e.g., function/thread/process/procedure
     */
    public String checkExistenceAddMethod(String methodName, String type, String location){
        
        int type_int = getType(type);
        int parentFrameNo = frameStack.size() - 2;
        Frame parentFrame = (Frame)frameStack.get(parentFrameNo);
        int currentFrameNo = frameStack.size() - 1;
        Frame curr_frame = (Frame)frameStack.get(currentFrameNo);
        int noOfParametersOfCurrentFrame = curr_frame.getNoOfParameters();
        boolean found = false;
        
        found = parentFrame.searchsymbol(methodName, type_int, noOfParametersOfCurrentFrame);
        if(found == false)
            parentFrame.addsymbol(methodName, type_int, noOfParametersOfCurrentFrame, "");
        else
        {
            System.out.println("Error at " + location +  ": Symbol \"" + methodName + "\" already exists.");
            System.exit(0);
        }
        return "";
    }
    public void checkLabelExistence(String labelName)
    {
        Frame mainFrame = (Frame)frameStack.get(0);
        if(!mainFrame.searchsymbol(labelName, VARIABLE, 0))
        {
            if(!labelNameList.contains(labelName))
            {
                labelNameList.add(labelName);
            }
            else
            {
                throwExceptionAndExit(new Exception("Label name \""+labelName+"\" already exists as a label."));
            }
        }
        else
        {
            throwExceptionAndExit(new Exception("Label name \""+labelName+"\" already exists as a global variable."));
        }
    }
    /**
    * This function removes the last frame, and it is called when a method is exited.
    */
    public void popLastFrame(){
      int lastFrameNum = frameStack.size()-1;
      if(lastFrameNum > 0)
	  {
          Frame f = frameStack.remove(lastFrameNum);
		  removedFrames.add(f);
	  }
    }
    /**
     * It shows list of warnings the were found during parsing phase.
     */
    public void showWarnings(){
            for (Iterator iter = warnings.entrySet().iterator(); iter.hasNext();)
            {
                Map.Entry entry = (Map.Entry)iter.next();
                String key = (String)entry.getKey();
                System.out.print(key);
            }
    }
    /**
     * This function takes an exception and displays its message, then it exits 
     * the program.
     * @param e It is the exception.
     */
    private void throwExceptionAndExit(Exception e){
        System.out.println("Exception occured: " + e.getMessage());
        System.exit(1);
    }
    /**
     * It returns the corresponding integer value for a string value e.g.,
     * for variable it returns a constant VARIABLE
     * @see VARIABLE,CONSTANT,PARAMETER,FUNCTION,PROCEDURE,THREAD,PROCESS
     */
    private int getType(String type){
    int value = 0;
    if(type.compareToIgnoreCase("variable") == 0)
        value = VARIABLE;
    else if(type.compareToIgnoreCase("function") == 0)
        value = FUNCTION;
    else if(type.compareToIgnoreCase("definition") == 0)
        value = DEFINITION;
    else if(type.compareToIgnoreCase("process") == 0)
        value =  PROCESS;
    else if(type.compareToIgnoreCase("thread") == 0)
        value =  THREAD;
    else if(type.compareToIgnoreCase("procedure") == 0)
        value =  PROCEDURE;
    else if(type.compareToIgnoreCase("constant") == 0)
        value =  CONSTANT;
    else if(type.compareToIgnoreCase("parameter") == 0)
        value =  PARAMETER;
    else if(type.compareToIgnoreCase("algorithm") == 0)
        value =  ALGORITHM;
    return value;
    }
    
    //-------------------Functions for PcalTranslator---------------------//
    
    /**
     * It retrieves the label information.
     * @param name              It is the name of the method.
     * @param type              It is the type of the method.
     * @param noOfParameters    It is the number of parameters.
     * @return                  It returns the label name.
     */
    public String getLabelInformation(String name, String type, int noOfParameters)
    {
        int type_int = getType(type);
        Frame f = null;
        f = getFrame(name, type_int, noOfParameters);
        String labelName = "";
        try
        {
            if(f != null)
                labelName = f.getLabelInformation(name, type_int, noOfParameters);
            else
                throw new Exception("getLabelInformation(..):Unable to find corresponding symbol.");
        }
        catch(Exception e)
        {
            throwExceptionAndExit(e);
        }
        
        return labelName;
    }
    /**
     * It updates the label information.
     * @param name              It is the name of the method.
     * @param type              It is the type of the method.
     * @param noOfParameters    It is the number of parameters.
     * @param labelName         It is the name of the label.
     */
    public void setLabelInformation(String name, String type, int noOfParameters, String labelName)
    {
        int type_int = getType(type);
        Frame f = null;
        f = getFrame(name, type_int, noOfParameters);
        try
        {
            if(f != null)
                f.setLabelInformation(name, type_int, noOfParameters, labelName);
            else
                throw new Exception("setLabelInformation(..):Unable to find corresponding symbol.");
        }
        catch(Exception e)
        {
            throwExceptionAndExit(e);
        }//******************************************************************//
    }
    /**
     * It updates the list of variable and method declarations.
     */
    public void updateDeclarations()
    {
      int lastFrameNum = frameStack.size()-1;
      if(lastFrameNum >= 1)
      {
        int parentFrameNum = lastFrameNum-1;
        Frame parentFrame = frameStack.get(parentFrameNum);
        Frame lastFrame = frameStack.get(lastFrameNum);
        parentFrame.setDeclarations(lastFrame.getName(), lastFrame.getType(), lastFrame.getNoOfParameters(), lastFrame.map);
        
      }
    }
    /**
     * It retrieves the list of variables for a given method(function/thread...).
     * @param name              It is the name of the method.
     * @param type              It is the type of the method.
     * @param noOfParameters    It is the number of parameters.
     * @return
     */
    public Map getVarDeclarations(String name, String type, int noOfParameters)
    {
        int type_int = getType(type);
        Frame f = null;
        Map varList = null;
        
        f = getFrame(name, type_int, noOfParameters);
        
        if(f != null)
        {
            try
            {
                varList = f.getVarDeclarations(name, type_int, noOfParameters);
            }
            catch(Exception e)
            {
                throwExceptionAndExit(e);
            }
        }
        else
            return null;
        
        return varList;
    }
    /**
     * It searches for the frame that contains the declaration of corresponding symbol.
     * @param name              It is the name of the method.
     * @param type              It is the type of the method.
     * @param noOfParameters    It is the number of parameters.
     * @return                  It returns frame.
     */
    private Frame getFrame(String name, int type, int noOfParameters)
    {
        int frame_no = frameStack.size() - 1;
        Frame f = null;
        boolean found = false;
        while(frame_no >= 0)
        {
            f = (Frame)frameStack.get(frame_no);
            found = f.searchsymbol(name, type, noOfParameters);
            if(found)
            {
                break;
            }
            frame_no--;
        }
        if(!found)
            return null;
        else
            return f;
    }
    /**
     * It retrieves the information regarding the scope of any given symbol.
     * @param symbol            It is the name of the method.
     * @param type              It is the type of the method.
     * @param noOfParameters    It is the number of parameters.
     * @return                  It return scope type, process name,..
     */
    public String[] getScopeInformation(String symbol, String type, int noOfParameters)
    {
      int type_int = getType(type);
      int frame_no = frameStack.size() - 1;
      Frame f;
      boolean found = false;
      String scope[] = new String[3];
      scope[0] = "";
      scope[1] = "";
      scope[2] = "";
      //if the symbol belongs to temporay bound variables then don't search in the symbol table.
		if(auxVariables.contains(symbol))
		{
			scope[1] = "auxillaryVariable";
			return scope;
		}
      //check if its a name of a process at that level but not yet declared.
      f = (Frame) frameStack.get(frame_no);
      if(f.processNames.contains(symbol))
      {
            scope[1] = "NotDeclaredProcessName";
            return scope;
      }

      while(frame_no >= 0)
      {
        f = (Frame)frameStack.get(frame_no);
        found = f.searchsymbol(symbol, type_int, noOfParameters);
        if(found)
        {
            if(f.getType() == FUNCTION || f.getType() == PROCEDURE )
            {
                scope[1] = "function";
            }
            else if(f.getType() == DEFINITION )
            {
                scope[1] = "definition";
            }
            else if(f.getType() == PROCESS)
            {
                scope[0] = f.getName();
                scope[1] = "process";
            }
            else if(f.getType() == THREAD)
            {
                scope[1] = "thread";
                scope[2] = f.getName();
            }
            else if(f.getType() == ALGORITHM)
            {
                scope[1] = "algorithm";
            }
            break;
        }
        else
        {//Check if its the name of a process or procedure (a frame in symbol table)
            String frameName = f.getOriginalName();
            if(frameName.equals(symbol))
            {
                scope[0] = f.getName();
                scope[2] = "ProcessID";
                break;
            }
        }
        frame_no--;
      }
      Frame parentFrame;
      if(frame_no == 1)//****
      {
          parentFrame = frameStack.get(1);
          scope[0] = parentFrame.getName();
      }
      return scope;
    }
    public void copyCurrentProcessNames(ArrayList<String> list)
    {
        int frame_no = frameStack.size() - 1;
        Frame f = frameStack.get(frame_no);
        for(int i=0;i<list.size();i++)
        {
            (f.processNames).add(list.get(i));
        }
    }
	/*
		Adds process name along with parent process's name in the list ASSUMING that the process names are not repeated in the algorithm.
		*/
	public void setProcessParentRelationship(String processName, String parentName)
	{
		processParentRelationList.put(processName, parentName);
	}
	/*
		This function returns the name of the parent process for a given process ASSUMING that the process names are not repeated in the algorithm.
		*/
	public String getParentName(String processName)
	{
		return processParentRelationList.get(processName);
	}
    /**
     * It confirms the declaration of a variable in the given process.
     * @param processName            It is the name of the process.
     * @param variableName           It is the name of the variable.
     * @return                  	 It returns true if variable is declared in the given process otherwise false.
     */
	public 	boolean confirmDeclaration(String processName, String variableName)
	{
        Frame f = null;//frameStack.get(frame_no);

		if(processName.equals("A1"))	//If its looking for a globally defined variable A1 is the name of the main frame representing the algorithm
		{
			if(frameStack.size() > 0)
			{
				f = frameStack.get(0);
			}
			if(auxVariables.contains(variableName))
				return true;
			else
				return f.searchsymbol(variableName, getType("variable"), 0);
		}
		else if((frameStack.get(frameStack.size()-1)).name == processName)	// If looking for variable in the current process
		{
			f = frameStack.get(frameStack.size()-1);
			return f.searchsymbol(variableName, getType("variable"), 0);
		}
		else	// If looking for variable declaration in the child processes 
		{
	        int frame_no = removedFrames.size() - 1;
	        while(frame_no >= 0)
	        {
	            f = (Frame)removedFrames.get(frame_no);
	            if(f.name == processName)
	            {
	                break;
	            }
	            frame_no--;
	        }
            if(f.name == processName)
            {
				return f.searchsymbol(variableName, getType("variable"), 0);
            }
		}
		return false;
		
	}

}