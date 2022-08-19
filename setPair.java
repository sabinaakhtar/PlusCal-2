

public class setPair {
    
    public String setName;
    public String parentSetName;
    public setPair(String s, String p){
        setName = s;
        if(p != null)
            parentSetName = p;
        else
            parentSetName = "";
    }
}
