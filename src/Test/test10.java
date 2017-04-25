
import com.google.common.io.Files;
import edu.stanford.nlp.ling.CoreAnnotations;
import edu.stanford.nlp.ling.CoreLabel;
import edu.stanford.nlp.ling.HasWord;
import edu.stanford.nlp.ling.TaggedWord;
import edu.stanford.nlp.parser.nndep.DependencyParser;
import edu.stanford.nlp.parser.nndep.demo.DependencyParserDemo;
import edu.stanford.nlp.pipeline.Annotation;
import edu.stanford.nlp.pipeline.StanfordCoreNLP;
import edu.stanford.nlp.process.DocumentPreprocessor;
import edu.stanford.nlp.tagger.maxent.MaxentTagger;
import edu.stanford.nlp.trees.GrammaticalStructure;
import edu.stanford.nlp.trees.TreePrint;
import edu.stanford.nlp.trees.TypedDependency;
import edu.stanford.nlp.util.CoreMap;
import edu.stanford.nlp.util.logging.Redwood;
import edu.stanford.nlp.pipeline.*;
import edu.stanford.nlp.ling.*; 
import edu.stanford.nlp.ling.CoreAnnotations.*; 
import edu.stanford.nlp.simple.*;
import edu.stanford.nlp.pipeline.MorphaAnnotator;
import org.tartarus.snowball.SnowballStemmer; 
import org.tartarus.snowball.ext.englishStemmer; 

import java.nio.charset.Charset;
import static java.util.Date.parse;
import java.util.*;
import java.io.*;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Rectangle;
import java.awt.Shape;
import java.awt.geom.Ellipse2D;
import java.awt.geom.Point2D;
import javax.swing.JFrame;
import org.apache.commons.collections15.Transformer;
import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.DefaultModalGraphMouse;
import edu.uci.ics.jung.visualization.control.ModalGraphMouse;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;
import java.lang.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.table.DefaultTableModel;
import javax.swing.JFrame;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.SwingUtilities;
import Test.*;
/**
 * Demonstrates how to first use the tagger, then use the NN dependency
 * parser. Note that the parser will not work on untagged text.
 *
 * @author Jon Gauthier
 */
//import opennlp.tools.lemmatizer.SimpleLemmatizer;


public class test10 extends JFrame{
    private JFrame mainFrame;
   private JLabel headerLabel;
   private JLabel statusLabel;
   private JPanel controlPanel;
   static String filename="",stradd="",filename1="";
   static String inputstr="";
   static int choice=0,tval=0,chval=0;
   public static synchronized void incrementCount() {
        choice++;
    }
   public static synchronized void incrementChoice(int num) {
        chval+=num;
    }
   private void prepareGUI(){
      mainFrame = new JFrame("Java Swing Examples");
      mainFrame.setSize(400,400);
      mainFrame.setLayout(new GridLayout(3, 1));
      
      mainFrame.addWindowListener(new WindowAdapter() {
         public void windowClosing(WindowEvent windowEvent){
            System.exit(0);
         }        
      });    
      headerLabel = new JLabel("", JLabel.CENTER);        
      statusLabel = new JLabel("",JLabel.CENTER);    
      statusLabel.setSize(350,100);

      controlPanel = new JPanel();
      controlPanel.setLayout(new FlowLayout());

      mainFrame.add(headerLabel);
      mainFrame.add(controlPanel);
      mainFrame.add(statusLabel);
      mainFrame.setVisible(true);  
   }
   public void showFileChooserDemo(){
      headerLabel.setText("Choose file which contains "+stradd); 
      final JFileChooser  fileDialog = new JFileChooser();
      JButton showFileDialogButton = new JButton("Open File");
      JButton showCloseDialogButton = new JButton("OK");
      showFileDialogButton.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            int returnVal = fileDialog.showOpenDialog(mainFrame);
            
            if (returnVal == JFileChooser.APPROVE_OPTION) {
               java.io.File file = fileDialog.getSelectedFile();
               statusLabel.setText("File Selected :" + file.getAbsolutePath());
                //System.out.println("File = "+file.getAbsolutePath());
                
                filename=file.getAbsolutePath();
            } else {
               statusLabel.setText("Open command cancelled by user." );           
            }      
         }
      });
      showCloseDialogButton.addActionListener(new ActionListener() {
    public void actionPerformed(ActionEvent e)
    {
        incrementCount();
       mainFrame.dispose();
    }
});
      controlPanel.add(showFileDialogButton);
      controlPanel.add(showCloseDialogButton);
      mainFrame.setVisible(true);  
   }
   public test10(){
      prepareGUI();
   }
final static int INF = 99999;
    static int dist[][] = new int[2000][2000];
    void floydWarshall(int graph[][],int V)
    {
        
        int i, j, k;
 
        /* Initialize the solution matrix same as input graph matrix.
           Or we can say the initial values of shortest distances
           are based on shortest paths considering no intermediate
           vertex. */
        for (i = 1; i < V; i++)
            for (j = 1; j < V; j++)
                dist[i][j] = graph[i][j];
 
        /* Add all vertices one by one to the set of intermediate
           vertices.
          ---> Before start of a iteration, we have shortest
               distances between all pairs of vertices such that
               the shortest distances consider only the vertices in
               set {0, 1, 2, .. k-1} as intermediate vertices.
          ----> After the end of a iteration, vertex no. k is added
                to the set of intermediate vertices and the set
                becomes {0, 1, 2, .. k} */
        for (k = 1; k < V; k++)
        {
            // Pick all vertices as source one by one
            for (i = 1; i < V; i++)
            {
                // Pick all vertices as destination for the
                // above picked source
                for (j = 1; j < V; j++)
                {
                    // If vertex k is on the shortest path from
                    // i to j, then update the value of dist[i][j]
                    if (dist[i][k] + dist[k][j] < dist[i][j])
                        dist[i][j] = dist[i][k] + dist[k][j];
                }
            }
        }
 
        // Print the shortest distance matrix
        //printSolution(dist,V);
    }
 public static int countwords(String s){

    int wordCount = 0;

    boolean word = false;
    int endOfLine = s.length() - 1;

    for (int i = 0; i < s.length(); i++) {
        // if the char is a letter, word = true.
        if (Character.isLetter(s.charAt(i)) && i != endOfLine) {
            word = true;
            // if char isn't a letter and there have been letters before,
            // counter goes up.
        } else if (!Character.isLetter(s.charAt(i)) && word) {
            wordCount++;
            word = false;
            // last word of String; if it doesn't end with a non letter, it
            // wouldn't count without this.
        } else if (Character.isLetter(s.charAt(i)) && i == endOfLine) {
            wordCount++;
        }
    }
    return wordCount;
}
    void printSolution(int dist[][],int V)
    {
        System.out.println("Following matrix shows the shortest "+
                         "distances between every pair of vertices");
        for (int i=1; i<V; ++i)
        {
            for (int j=1; j<V; ++j)
            {
                if (dist[i][j]==INF)
                    System.out.print("INF ");
                else
                    System.out.print(dist[i][j]+"   ");
            }
            System.out.println();
        }
    }
  /** A logger for this class */
  //private static Redwood.RedwoodChannels log = Redwood.channels(DependencyParserDemo.class);

  public static void main(String[] args) throws IOException {
    String modelPath = DependencyParser.DEFAULT_MODEL;
    
    Scanner sc=new Scanner(System.in);
     String taggerPath = "edu/stanford/nlp/models/pos-tagger/english-left3words/english-left3words-distsim.tagger";
    for (int argIndex = 0; argIndex < args.length; ) {
      switch (args[argIndex]) {
        case "-tagger":
          taggerPath = args[argIndex + 1];
          argIndex += 2;
          break;
        case "-model":
          modelPath = args[argIndex + 1];
          argIndex += 2;
          break;
        default:
          throw new RuntimeException("Unknown argument " + args[argIndex]);
      }
    }
    MaxentTagger tagger = new MaxentTagger(taggerPath);
    DependencyParser parser = DependencyParser.loadFromModelFile(modelPath);
    int choice1=0;
    do
    {   
    int trueval=0,goodacc=0;
    double possent[]=new double[2000],negsent[]=new double[2000];
    String fullsent[]=new String[2000];
    filename="";stradd="";filename1="";
   inputstr="";
   choice=0;tval=0;chval=0;
   final JFrame f2 = new JFrame("Enter the text");
    f2.setSize(1500,1500);
      f2.getContentPane().setLayout(new GridLayout(3, 1));
      JButton option1 = new JButton("User text Input");
      JButton option2 = new JButton("Check Accuracy using preclassified text");
      JButton option3 = new JButton("Take input from existing file");
      JButton option4 = new JButton("Exit");
      option1.addActionListener(new ActionListener() {
    public void actionPerformed(ActionEvent e)
    {
        incrementChoice(1);
       f2.dispose();
    }
});
      option2.addActionListener(new ActionListener() {
    public void actionPerformed(ActionEvent e)
    {
        incrementChoice(2);
       f2.dispose();
    }
});
      option3.addActionListener(new ActionListener() {
    public void actionPerformed(ActionEvent e)
    {
        incrementChoice(3);
       f2.dispose();
    }
});
      option4.addActionListener(new ActionListener() {
    public void actionPerformed(ActionEvent e)
    {
        incrementChoice(4);
       f2.dispose();
    }
});
    //f1.getContentPane().setLayout(new FlowLayout());
    //f1.add(new JScrollPane(table));
    //f1.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);  
    f2.add(option1);
    f2.add(option2);
    f2.add(option3);
    f2.add(option4);
        f2.pack();
        f2.setVisible(true);
     while(true)
         {
             if(chval>0)
             {
                 //System.out.println(" New val = "+chval);
                 //System.out.println("Done!!");
                 break;
             }
             else
                 System.out.print("");
         }  
      System.out.println("Enter your choice\n1.User input\n2.Check for accuracy with preclassified data\n3.Take input from existing file\n4.Exit the program\n");
      choice1=chval;
      if(choice1==1)
      {
          try {
        UIManager.setLookAndFeel("com.sun.java.swing.plaf.windows.WindowsLookAndFeel");
    } catch (Exception evt) {}
  
    final JFrame f = new JFrame("Enter the text");
    f.setSize(800,800);
      //f.setLayout(new GridLayout(3, 1));
    f.getContentPane().setLayout(new FlowLayout());
    //f.getContentPane().add(new JTextField("Text field 1"));
    //f.getContentPane().add(new JTextField("Text field 2", 8));
    //JTextField t = new JTextField("Text field 3", 8);
    //t.setHorizontalAlignment(JTextField.RIGHT);
    //f.getContentPane().add(t);
    final JTextField t = new JTextField("Text field 4", 100);
    t.setHorizontalAlignment(JTextField.CENTER);
    f.getContentPane().add(t);
    JButton close = new JButton("OK");
    f.getContentPane().add(close);
    //f.getContentPane().add(new JTextField("Text field 5", 3));
     close.addActionListener(new ActionListener() {
    public void actionPerformed(ActionEvent e)
    {
        inputstr=t.getText();
        incrementCount();
        System.out.println("Text = "+inputstr);
       f.dispose();
    }
});
    f.pack();
    f.setVisible(true);
         while(true)
         {
             if(choice==1)
             {
                 System.out.println("Input = "+inputstr);
                 //System.out.println("Done!!");
                 break;
             }
             else
                 System.out.print("");
         }
         Reader reader = new StringReader(inputstr);
         DocumentPreprocessor dp = new DocumentPreprocessor(reader);
java.util.List<String> sentenceList = new ArrayList<String>();
for (java.util.List<HasWord> sentence : dp) {
   // SentenceUtils not Sentence
   String sentenceString = SentenceUtils.listToString(sentence);
   sentenceList.add(sentenceString);
}
          //System.out.println("Maybe??");
          int c45=0;
          String inp[]=new String[5000];
for(String word:sentenceList)
{
              System.out.println(" "+word);
              inp[c45]=word;
              c45++;
}
          //System.out.println("Cou = "+c45);
/*PrintWriter out = new PrintWriter("E:\\store.txt");
for (String word: sentenceList) {
        out.println(word);
    }*/
int k;
        try(  PrintWriter out = new PrintWriter( "E:\\store.txt" )  ){
    for(k=0;k<c45;k++)
    {
        out.println(inp[k]);
    }
}
         filename1="E:\\store.txt";
         filename="E:\\polarity.txt";
      }
      else if(choice1==2)
      {
    stradd="test sentences";
     test10  swingControlDemo = new test10();      
      swingControlDemo.showFileChooserDemo();
      stradd=" polarity for test sentences";
      while(true)
      {
          if(choice==1)
          {
              //System.out.println("Broken :)");
              filename1=filename;
      test10  swingControlDemo1 = new test10();      
      swingControlDemo1.showFileChooserDemo(); 
      break;
          }
          else
              System.out.print("");
      }
      while(true)
      {
          if(choice==2)
              break;
          else
              System.out.print("");
      }
      System.out.println("Filename 1 = "+filename1+" Filename = "+filename);
      }
      else if(choice1==3)
      {
          stradd="test sentences";
          test10  swingControlDemo = new test10();      
      swingControlDemo.showFileChooserDemo();
      while(true)
      {
          if(choice==1)
          {
              //System.out.println("Broken :)");
              filename1=filename;
      break;
          }
          else
              System.out.print("");
      }
      filename="E:\\polarity.txt";
      }
      else
      {
          System.exit(0);
      }
   
     FileInputStream fis = new FileInputStream("E:\\stopwords.txt");
 
	//Construct BufferedReader from InputStreamReader
	BufferedReader br = new BufferedReader(new InputStreamReader(fis));
        String stop[]=new String[2000];
        int stopcount=0;
	String line = null;
	while ((line = br.readLine()) != null) {
		stop[stopcount]=line;
                stopcount++;
	}
        br.close();
        //System.out.println("Enter choice ");
        int ch,i,unique;
        //ch=sc.nextInt();
        //System.out.println("File selected = "+filename);
        String str5[]=new String[50000];
        int polarity1[]=new int[50000];
        int count1=0,positive=0,negative=0,totalpos=0,totalneg=0;
        /*if(ch==1)
        {
        FileInputStream fis1 = new FileInputStream("E:\\trainpos.txt");
FileInputStream fis2 = new FileInputStream("E:\\trainneg.txt");	//Construct BufferedReader from InputStreamReader
	BufferedReader br1 = new BufferedReader(new InputStreamReader(fis1));
	String line1 = null;
        
	while ((line1 = br1.readLine()) != null) {
		str5[count1]=line1;
                polarity1[count1]=1;
                positive++;
                totalpos+=countwords(str5[count1]);
                count1++;
	}
        System.out.println("Tcount = "+count1);
        br1.close();
        BufferedReader br2 = new BufferedReader(new InputStreamReader(fis2));
	String line2 = null;
	while ((line2 = br2.readLine()) != null) {
		str5[count1]=line2;
                polarity1[count1]=0;
                negative++;
                totalneg+=countwords(str5[count1]);
                count1++;
	}
        System.out.println("Tcount = "+count1);
        br2.close();
        File f = new File("E:\\fulltrain.txt");
        ArrayList arr=new ArrayList();
        HashMap<String, Integer> listOfWords = new HashMap<String, Integer>(); 
        Scanner in = new Scanner(f);
        i=0;
        while(in.hasNext())
        {
        String s=in.next();
        //System.out.println(s);
        arr.add(s);
        }
        Iterator itr=arr.iterator();
        while(itr.hasNext())
        {i++;

            listOfWords.put((String) itr.next(), i);
            //System.out.println(listOfWords);
        }

        Set<Object> uniqueValues = new HashSet<Object>(listOfWords.values()); 
        unique=uniqueValues.size();
        System.out.println("Unique words = "+unique);
        }*/
        
        FileInputStream fis3 = new FileInputStream("E:\\imdb.txt");
 
	//Construct BufferedReader from InputStreamReader
	BufferedReader br3 = new BufferedReader(new InputStreamReader(fis3));
	String line3 = null;
	while ((line3 = br3.readLine()) != null) {
		str5[count1]=line3.substring(0,line3.length()-1).toLowerCase();
                polarity1[count1]=(int)(line3.charAt(line3.length()-1))-48;
                if(polarity1[count1]==0)
                {
                    negative++;
                    totalneg+=countwords(str5[count1]);
                }
                else
                {
                    positive++;
                    totalpos+=countwords(str5[count1]);
                }
                count1++;
	}
        br3.close();
        File f = new File("E:\\imdb.txt");
        ArrayList arr=new ArrayList();
        HashMap<String, Integer> listOfWords = new HashMap<String, Integer>(); 
        Scanner in = new Scanner(f);
        i=0;
        while(in.hasNext())
        {
        String s=in.next();
        //System.out.println(s);
        arr.add(s);
        }
        Iterator itr=arr.iterator();
        while(itr.hasNext())
        {
            i++;

            listOfWords.put((String) itr.next(), i);
            //System.out.println(listOfWords);
        }

        Set<Object> uniqueValues = new HashSet<Object>(listOfWords.values()); 
        unique=uniqueValues.size();
        System.out.println("Unique words = "+unique);
            
            
        //System.out.println(" Count1 = "+count1+" Pos = "+positive+" Neg = "+negative+" Total positive = "+totalpos+" Total negative = "+totalneg);
        /*for(i=0;i<10;i++)
        {
            System.out.println("Str = "+str5[i]+" Polarity = "+polarity1[i]);
        }*/
    File inputFile = new File(filename1);/////////////////////////////////////////////////////////////////////////////////////////////////////////
    String text = Files.toString(inputFile, Charset.forName("UTF-8"));
 /*Properties props = new Properties();
props.setProperty("annotators","tokenize, ssplit, pos");
StanfordCoreNLP pipeline = new StanfordCoreNLP(props);
Annotation annotation = new Annotation(text);
pipeline.annotate(annotation);
43
        pipeline.annotate(annotation);*/
    

    DocumentPreprocessor tokenizer = new DocumentPreprocessor(new StringReader(text));
    int linenum = 0;
      //System.out.println("Filename = "+filename);
    FileInputStream fis4 = new FileInputStream(filename);//Construct BufferedReader from InputStreamReader
	BufferedReader br4 = new BufferedReader(new InputStreamReader(fis4));
	String line4 = null;
        int pole[]=new int[10000];
        int pcount=0;
	while ((line4 = br4.readLine()) != null) {
		pole[pcount]=Integer.parseInt(line4);
                pcount++;
	}
    for (java.util.List<HasWord> sentence : tokenizer) {
        System.out.println("Line Num = "+linenum);
        
        java.util.List<String> lemmas = new LinkedList<String>();
        String word[]=new String[2000],tag[]=new String[2000],str1;
 int m=1;
 String negation[]=new String[2000];
            int negcount=0;
      java.util.List<TaggedWord> tagged = tagger.tagSentence(sentence);
       
        //System.out.println(tagged);
        for(i=0;i<tagged.size();i++)
        {
            System.out.println(tagged.get(i));
            str1=tagged.get(i).toString();
            word[m]=str1.substring(0,str1.indexOf("/"));
            tag[m]=str1.substring(str1.indexOf("/")+1,str1.length());
            m++;
        }
      GrammaticalStructure gs = parser.predict(tagged);
java.util.List<TypedDependency> tdl = gs.typedDependenciesCCprocessed();
System.out.println(tdl);
        //System.out.println("String = "+text);
        //fullsent[linenum]=text;
        
        
        //System.out.println("One by one");
        String str2,str3;/////Extract position from dependencies
        char ch1;
        int adj[][]=new int[2000][2000],pos1,pos2,j,count=0;
        String rel[]=new String[2000],start[]=new String[2000],end[]=new String[2000];
        for(i=0;i<tdl.size();i++)
        {
            //System.out.println(tdl.get(i));
            str1=tdl.get(i).toString();
            pos1=str1.indexOf(",",1);
            //System.out.println("Pos 1 = "+pos1);
            str2="";str3="";
            for(j=pos1-1;j>=0;j--)
            {
                ch1=str1.charAt(j);
                if((int)ch1>=48&&(int)ch1<=57)
                {
                    str2+=ch1;
                }
                else
                    break;
            }
            String reverse = new StringBuffer(str2).reverse().toString();
            str2=reverse;
            
            for(j=str1.length() -2;j>=0;j--)
            {
                 ch1=str1.charAt(j);
                if((int)ch1>=48&&(int)ch1<=57)
                {
                    str3+=ch1;
                }
                else
                    break;
            }
            reverse = new StringBuffer(str3).reverse().toString();
            str3=reverse;
            pos2=str1.indexOf("(",1);
            
            rel[count]=str1.substring(0,pos2);
            if(rel[count].equals("root"))
            {
                //System.out.println("No need!!!");
            }
            else
            {
            start[count]=word[Integer.parseInt(str2)];
            end[count]=word[Integer.parseInt(str3)];
            //System.out.println("Str 2 = "+str2+" Str 3 = "+str3);
            //System.out.println(" Relation = "+str1.substring(0,pos2)+" Start = "+start[count]+" End = "+end[count]);
            if(str1.substring(0,pos2).equals("neg"))
            {
                negation[negcount]=start[count];
                negcount++;
            }
            count++;
            } 
            //System.out.println("Pos1 str = "+str2+"  Pos2 str = "+str3);
            adj[Integer.parseInt(str2)][Integer.parseInt(str3)]=1;
            adj[Integer.parseInt(str3)][Integer.parseInt(str2)]=1;
            
        }
        String fea[]=new String[2000];
        int feacount=0,feapos[]=new int[2000];
        for(i=1;i<m;i++)
        {
            //System.out.println("Word = "+word[i]+"  Tag = "+tag[i]);
            if(tag[i].charAt(0)=='N')
            {
                fea[feacount]=word[i];
                feapos[feacount]=i;
                feacount++;
            }
        }
        int val=10;
        //System.out.format("%8s"," ");
        //for(i=1;i<m;i++)
            //System.out.format("%8s",word[i]);
        //System.out.println("");
        for(i=1;i<m;i++)
        {
           // System.out.format("%8s",word[i]);
            for(j=1;j<m;j++)
            {
                
                if(adj[i][j]==0&&(i!=j))
                    adj[i][j]=99999;
                //System.out.format("%8s",adj[i][j]);
            }
            //System.out.println("");
        }
        test9 a = new test9();
        a.floydWarshall(adj,m-1);
        //System.out.println("Val = "+dist[1][3]);
        //System.out.println("Ok upto here!!");
        //System.out.println("Feature count= "+feacount);
        /*for(i=0;i<feacount;i++)
        {
            System.out.println("Feature = "+fea[i]);
        }*/
        int comb[]=new int[1000],combcount=1;
        comb[0]=feapos[0];
       
        String clus[]=new String[2000];
        int cluspos[]=new int[2000];
        int maxdist[]=new int[2000];
        for(i=1;i<m;i++)
        {
            maxdist[i]=99999;
            if(tag[i].charAt(0)=='N')
            {
                clus[i]=word[i];
                maxdist[i]=0;
                cluspos[i]=i;
            }
            else
            {
                for(j=0;j<feacount;j++)
                {
                    if(dist[i][feapos[j]]<maxdist[i])
                    {
                        maxdist[i]=dist[i][feapos[j]];
                        clus[i]=fea[j];
                        cluspos[i]=feapos[j];
                        
                    }
                }
                //adj1[i][cluspos[i]]=1;
                //adj1[cluspos[i]][i]=1;
            }
            //System.out.println("Word = "+word[i]+" Cluster = "+clus[i]+" Dist = "+maxdist[i]+" Clusposition = "+cluspos[i]);
            
        }
        String feature[]=new String[2000];
        int actpos[]=new int[2000];
        int fcount=1,fwords[]=new int[2000],wordcount=0;
        fwords[0]=feapos[0];
        //fwords stores the indices which may be combined..
        for(i=1;i<feacount;i++)
        {
            if(dist[feapos[0]][feapos[i]]<3)
            {
                fwords[fcount]=feapos[i];
                fcount++;
            }
        }
        /*System.out.println("Fcount= "+fcount);
        for(i=0;i<fcount;i++)
        {
            System.out.println("Pos = "+fwords[i]);
        }*/
        for(i=1;i<m;i++)
        {
            for(j=0;j<fcount;j++)
            {
                if(cluspos[i]==fwords[j])
                {
                    feature[wordcount]=word[i];
                    actpos[wordcount]=i;
                    wordcount++;
                }
            }
        }
        for(i=0;i<wordcount;i++)
        {
            //System.out.println("Feature = "+feature[i]);
        }
        System.out.println("");
        SnowballStemmer snowballStemmer = new englishStemmer();
        String stem[]=new String[2000];
        for(i=0;i<wordcount;i++)
        {
            if(feature[i].charAt(feature[i].length()-1)=='y'||feature[i].charAt(feature[i].length()-1)=='Y'||feature[i].charAt(feature[i].length()-1)=='e'||feature[i].charAt(feature[i].length()-1)=='E')
            {
                stem[i]=feature[i];
            }
            else
            {
            snowballStemmer.setCurrent(feature[i]); 
            snowballStemmer.stem();
            
            stem[i]=snowballStemmer.getCurrent();
            }
            stem[i]=stem[i].toLowerCase();
            //System.out.println("  "+feature[i]+"  "+stem[i]);
        }
        //System.out.println("Total stop words = "+stopcount+" Stop[4] = "+stop[4]);
        String finalstr[]=new String[2000];
        int fincount=0;
        int flag=0;
        int pos[]=new int[2000];
        System.out.println("Stemmed features: -");
        for(i=0;i<wordcount;i++)
        {
            System.out.println("Feature = "+stem[i]);
        }
        //SS:- Remove stop words from stemmed words*******************************************
        //If the word is not a stop word,then we are storing it in the array finalstr[].****************
        for(i=0;i<wordcount;i++)
        {
            flag=0;
            for(j=0;j<stopcount;j++)
            {
              if(stem[i].equals(stop[j]))
              {
                  flag=1;
                  break;
              }
              
            }
            if(flag==1)
                ;
                //System.out.println(" Not needed "+stem[i]);
            else
            {
                finalstr[fincount]=stem[i];
                pos[fincount]=actpos[i];
                fincount++;
            }
        }
        //System.out.println("Fincount = "+fincount);
        //System.out.println("Final strings :- ");
        //Wa are trying to reverse the probability of words which are negated by a nnegation relationship*************
        int change[]=new int[2000];
        for(i=0;i<fincount;i++)
        {
            for(j=0;j<negcount;j++)
            {
                if(negation[j].equals(finalstr[i]))
                {
                    change[i]=1;
                    break;
                }
            }
            //System.out.println(" "+finalstr[i]+" "+pos[i]+" Negative = "+change[i]);
            
        }
        System.out.println("Negative words = "+negcount);
        for(i=0;i<negcount;i++)
        {
            System.out.println("Neg word = "+negation[i]);
        }
        int pospres[]=new int[2000],negpres[]=new int[2000];
        double bayespos[]=new double[2000],bayesneg[]=new double[2000];
        //Actual Bayes Implementation....***********************************************
        //Count the values of P(word|+) and P(word|-)
        //str5[j] contains all the training set sentences.
        //Pospres[i] = No. of occurrences in +ve sentences.
        //Negpres[i] = No. of ocurrences in -ve sentences.
        for(i=0;i<fincount;i++)
        {
            for(j=0;j<count1;j++)
            {
                if(str5[j].contains(finalstr[i]))
                {
                    if(polarity1[j]==1)
                    {
                        pospres[i]++;
                    }
                    else
                    {
                       negpres[i]++; 
                    }
                }
            }
            //Actual formula**************************************************************
            bayespos[i]=(double)(pospres[i]+1)/(double)(unique+totalpos);
            bayesneg[i]=(double)(negpres[i]+1)/(double)(unique+totalneg);
            System.out.println("Str = "+finalstr[i]+" Pos count = "+pospres[i]+" Neg Count = "+negpres[i]);
            //System.out.println("Bayes pos = "+bayespos[i]+" Bayes neg = "+bayesneg[i]);
        }
        double posprob,negprob,prob;
        //We are finding out the prior probability of positive and negative sentences***********************
        posprob=(double)positive/(double)count1;
        negprob=1-posprob;
        prob=posprob/negprob;
        //System.out.println("Posprob = "+posprob+" Negprob = "+negprob);
        String addneg[]=new String[2000];
        int ncount=0;
        //Words with a negation relation have change[i]=1 and their probability of positive and negative has to be reversed.
        for(i=0;i<fincount;i++)
        {
            if(change[i]==1)
            {
                addneg[ncount]=finalstr[i];
                ncount++;
            }
        }
        //System.out.println(" Ncount = "+ncount);
        /*for(i=0;i<ncount;i++)
        {
            System.out.println(" Neg word = "+addneg[i]);
        }*/
        //System.out.println("Count of relations = "+count);
        //We are also making change[i]=1 for those words which have a direct relation witha nother word having word[i]=1******
        //Start[i]= initial word in dependency and end[i]= 2nd word in dependency
        String add1[]=new String[2000];int cadd1=0;
        for(i=0;i<count;i++)
        {
            //System.out.println("Start = "+start[i]+" End = "+end[i]);
            for(j=0;j<ncount;j++)
            {
                if(addneg[j].equals(start[i]))
                {
                    add1[cadd1]=end[i];
                    cadd1++;
                    
                }
                else if(addneg[j].equals(end[i]))
                        {
                          add1[cadd1]=start[i];
                          cadd1++;
                        }
            }
        }
        //System.out.println("Cadd1 = "+cadd1);
        /*for(i=0;i<cadd1;i++)
        {
            //System.out.println("Add this  : -"+add1[i]);
        }*/
        //Changing the values of change[i]********************************************
        for(i=0;i<fincount;i++)
        {
            if(change[i]==0)
            {
                for(j=0;j<cadd1;j++)
                {
                    if(finalstr[i].equals(add1[j]))
                    {
                        change[i]=1;
                        break;
                    }
                }
            }
            //if(change[i]==1)
                //System.out.println("Change this!! "+ finalstr[i]);
        }
        for(i=0;i<fincount;i++)
        {
            if(change[i]==0)
            prob*=bayespos[i]/bayesneg[i];
            else
                prob*=bayesneg[i]/bayespos[i];
        }
        //System.out.println("Prob = "+prob);
        //Calculate positive and negative sentiment*******************************
        double percent;
        percent=prob/(prob+1.0);
        System.out.println("Positive sentiment = "+(percent*100)+" Negative sentiment = "+(1-percent)*100);
        possent[linenum]=(percent*100);
        negsent[linenum]=100-(percent*100);
        int finpol;
        if(percent*100>50)
            finpol=1;
        else
            finpol=0;
        if(choice1==2)
        System.out.println("Finpol = "+finpol+" Pole = "+pole[linenum]);
        linenum++;
        if(finpol==pole[linenum])
        {
            trueval++;
            if(percent*100>70||percent*100<30)
                goodacc++;
        }
        
        
        
	
        
        ////Do all computations before this!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        /*DirectedSparseGraph<String, String> g = new DirectedSparseGraph<String, String>();
        for(i=1;i<m;i++)
        {
            g.addVertex(word[i]);
        }
    //g.addVertex("Square");
    //g.addVertex("Rectangle");
    //g.addVertex("Circle");
    //g.addEdge("Edge1", "Square", "Rectangle");
    //g.addEdge("Edge2", "Square", "Circle");
    String str4;
        System.out.println("");
    for(i=0;i<count;i++)
    {
        str4=i+rel[i];
        System.out.format("Str4 = %s Start = %s End = %s",str4,start[i],end[i]);
        System.out.println("");
    }
    for(i=0;i<count;i++)
    {
        str4=i+rel[i];
        g.addEdge(str4,start[i],end[i]);
    }
    VisualizationViewer<String, String> vv =
      new VisualizationViewer<String, String>(
        new CircleLayout<String, String>(g), new Dimension(1350,700));
    Transformer<String, String> transformer = new Transformer<String, String>() {
      @Override public String transform(String arg0) { return arg0; }
    };
    vv.getRenderContext().setVertexLabelTransformer(transformer);
    transformer = new Transformer<String, String>() {
      @Override public String transform(String arg0) { return arg0; }
    };
    vv.getRenderContext().setEdgeLabelTransformer(transformer);
    //vv.getRenderer().setVertexRenderer(new MyRenderer());
     JFrame frame = new JFrame();
    frame.getContentPane().add(vv);
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    frame.pack();
    frame.setVisible(true);
*/
    }
    //Used for diplaying output in file**********************************************
    //Calculating actual sentences***************************************************
    FileInputStream fis5 = new FileInputStream(filename1);
       int linecount=0;
	//Construct BufferedReader from InputStreamReader
	BufferedReader br5 = new BufferedReader(new InputStreamReader(fis5));
 
	String line5 = null;
	while ((line5 = br5.readLine()) != null) {
		fullsent[linecount]=line5;
                linecount++;
	}
 
	br.close();
        Object[][] data = new Object[linenum][3];
    for(i=0;i<linenum;i++)
    {
        System.out.println("Sentence = "+fullsent[i]);
        System.out.println("Positive = "+possent[i]+" Negative = "+negsent[i]);
        data[i][0]=possent[i];
        data[i][1]=negsent[i];
        data[i][2]=fullsent[i];
    }
    String[] columns = new String[] {
             "Positive","Negative","Sentence"
        };
         
        //actual data for the table in a 2d array
        /*{
            {1, "John Cena is back bitches!!He is coming back to WWE and will kill you all."},
            {2, "Rambo" },
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"},
            {3, "Zorro"},{3, "Zorro"},{3, "Zorro"},{3, "Zorro"}
        };*/
         
        final Class[] columnClass = new Class[] {
            Double.class, Double.class,String.class
        };
        //create table model with data
        DefaultTableModel model = new DefaultTableModel(data, columns) {
            @Override
            public boolean isCellEditable(int row, int column)
            {
                return false;
            }
            @Override
            public Class<?> getColumnClass(int columnIndex)
            {
                return columnClass[columnIndex];
            }
        };
         
        JTable table = new JTable(model);
        table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
        table.getColumnModel().getColumn(0).setPreferredWidth(50);
        table.getColumnModel().getColumn(1).setPreferredWidth(50);
        table.getColumnModel().getColumn(2).setMinWidth(1300);
        final JFrame f1 = new JFrame("Enter the text");
    //f1.setSize(800,800);
      f1.getContentPane().setLayout(new GridLayout(3, 1));
    //f1.getContentPane().setLayout(new FlowLayout());
    f1.add(new JScrollPane(table));
    //f1.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);       
        f1.pack();
        f1.setVisible(true);
    if(choice1==2)
    {
      System.out.println("True = "+trueval+" Lines = "+linenum+" Pcount = "+pcount);
      System.out.println("Total accuracy = "+((double)trueval/(double)linenum)*100);
      System.out.println("Good Accuracy(Above 70 % )"+((double)goodacc/(double)linenum)*100);
    }
    
  }
    while(choice1!=4);
  }
}
//[nsubj(phone-5, Samsung-1), cop(phone-5, is-2), det(phone-5, a-3), amod(phone-5, good-4), root(ROOT-0, phone-5), punct(phone-5, .-6)]