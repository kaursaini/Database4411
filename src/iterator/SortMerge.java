package iterator;

import heap.*;
import global.*;
import diskmgr.*;
import bufmgr.*;
import index.*;
import java.io.*;

/*==========================================================================*/
/**
 * Sort-merge join.
 * Call the two relations being joined R (outer) and S (inner).  This is an
 * implementation of the naive sort-merge join algorithm.  The external
 * sorting utility is used to generate runs.  Then the iterator interface
 * is called to fetch successive tuples for the final merge with joining.
 */

public class SortMerge extends Iterator implements GlobalConst {

    /**
     *constructor,initialization
     *@param in1[]         Array containing field types of R
     *@param len_in1       # of columns in R
     *@param s1_sizes      Shows the length of the string fields in R.
     *@param in2[]         Array containing field types of S
     *@param len_in2       # of columns in S
     *@param s2_sizes      Shows the length of the string fields in S
     *@param sortFld1Len   The length of sorted field in R
     *@param sortFld2Len   The length of sorted field in S
     *@param join_col_in1  The col of R to be joined with S
     *@param join_col_in2  The col of S to be joined with R
     *@param amt_of_mem    Amount of memory available, in pages
     *@param am1           Access method for left input to join
     *@param am2           Access method for right input to join
     *@param in1_sorted    Is am1 sorted?
     *@param in2_sorted    Is am2 sorted?
     *@param order         The order of the tuple: assending or desecnding?
     *@param outFilter[]   Ptr to the output filter
     *@param proj_list     Shows what input fields go where in the output tuple
     *@param n_out_flds    Number of outer relation fileds
     *@exception JoinNewFailed               Allocate failed
     *@exception JoinLowMemory               Memory not enough
     *@exception SortException               Exception from sorting
     *@exception TupleUtilsException         Exception from using tuple utils
     *@exception JoinsException              Exception reading stream
     *@exception IndexException              Exception...
     *@exception InvalidTupleSizeException   Exception...
     *@exception InvalidTypeException        Exception...
     *@exception PageNotReadException        Exception...
     *@exception PredEvalException           Exception...
     *@exception LowMemException             Exception...
     *@exception UnknowAttrType              Exception...
     *@exception UnknownKeyTypeException     Exception...
     *@exception IOException                 Some I/O fault
     *@exception Exception                   Generic
     */

    public SortMerge(
        AttrType    in1[], 
        int         len_in1,                        
        short       s1_sizes[],
        AttrType    in2[],                
        int         len_in2,                        
        short       s2_sizes[],

        int         join_col_in1,                
        int         sortFld1Len,
        int         join_col_in2,                
        int         sortFld2Len,

        int         amt_of_mem,               
        Iterator    am1,                
        Iterator    am2,                

        boolean     in1_sorted,                
        boolean     in2_sorted,                
        TupleOrder  order,

        CondExpr    outFilter[],                
        FldSpec     proj_list[],
        int         n_out_flds
    )
    throws JoinNewFailed ,
        JoinLowMemory,
        SortException,
        TupleUtilsException,
        JoinsException,
        IndexException,
        InvalidTupleSizeException,
        InvalidTypeException,
        PageNotReadException,
        PredEvalException,
        LowMemException,
        UnknowAttrType,
        UnknownKeyTypeException,
        IOException,
        Exception
    {
    } // End of SortMerge constructor

/*--------------------------------------------------------------------------*/
    /**
     *Reads a tuple from a stream in a less painful way.
     */
    private boolean readTuple(
        Tuple    tuple,
        Iterator tupleStream
    )
        throws JoinsException,
            IndexException,
            UnknowAttrType,
            TupleUtilsException,
            InvalidTupleSizeException,
            InvalidTypeException,
            PageNotReadException,
            PredEvalException,
            SortException,
            LowMemException,
            UnknownKeyTypeException,
            IOException,
            Exception
    {
        Tuple temp;
        temp = tupleStream.get_next();
        if (temp != null) {
            tuple.tupleCopy(temp);
            return true;
        } else {
            return false;
        }
    } // End of readTuple

/*--------------------------------------------------------------------------*/
    /**
     *Return the next joined tuple.
     *@return the joined tuple is returned
     *@exception IOException I/O errors
     *@exception JoinsException some join exception
     *@exception IndexException exception from super class
     *@exception InvalidTupleSizeException invalid tuple size
     *@exception InvalidTypeException tuple type not valid
     *@exception PageNotReadException exception from lower layer
     *@exception TupleUtilsException exception from using tuple utilities
     *@exception PredEvalException exception from PredEval class
     *@exception SortException sort exception
     *@exception LowMemException memory error
     *@exception UnknowAttrType attribute type unknown
     *@exception UnknownKeyTypeException key type unknown
     *@exception Exception other exceptions
     */

    public Tuple get_next() 
        throws IOException,
           JoinsException ,
           IndexException,
           InvalidTupleSizeException,
           InvalidTypeException, 
           PageNotReadException,
           TupleUtilsException, 
           PredEvalException,
           SortException,
           LowMemException,
           UnknowAttrType,
           UnknownKeyTypeException,
           Exception
    {
    } // End of get_next

/*--------------------------------------------------------------------------*/
    /** 
     *implement the abstract method close() from super class Iterator
     *to finish cleaning up
     *@exception IOException I/O error from lower layers
     *@exception JoinsException join error from lower layers
     *@exception IndexException index access error 
     */

    public void close() 
        throws JoinsException, 
            IOException
    {
    } // End of close

} // End of CLASS SortMerge

