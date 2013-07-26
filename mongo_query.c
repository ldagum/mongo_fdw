/*-------------------------------------------------------------------------
 *
 * mongo_query.c
 *
 * Function definitions for sending queries to MongoDB. These functions assume
 * that queries are sent through the official MongoDB C driver, and apply query
 * optimizations to reduce the amount of data fetched from the driver.
 *
 * Copyright (c) 2012, Citus Data, Inc.
 *
 * $Id$
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"
#include "mongo_fdw.h"

#include "catalog/pg_type.h"
#include "lib/stringinfo.h"
#include "nodes/makefuncs.h"
#include "nodes/relation.h"
#include "optimizer/var.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/date.h"
#include "utils/hsearch.h"
#include "utils/lsyscache.h"
#include "utils/numeric.h"
#include "utils/timestamp.h"

#include <string.h>
#include <assert.h>


/* Local functions forward declarations */
static Expr * FindArgumentOfType(List *argumentList, NodeTag argumentType);
static char * MongoOperatorName(const char *operatorName);
static List * EqualityOperatorList(List *operatorList);
static List * UniqueColumnList(List *operatorList);
static List * ColumnOperatorList(Var *column, List *operatorList);
static void AppendConstantValue(bson *queryDocument, const char *keyName,
								const bson_type toBsonType, Const *constant);
char** StrSplit(char* a_str, const char a_delim);

void my_bson_print_raw(const char *data , int depth );
void my_bson_print( const bson *b );


void my_bson_print_raw( const char *data , int depth ) {
    bson_iterator i;
    const char *key;
    int temp;
    bson_timestamp_t ts;
    char oidhex[25];
    bson scope;
    const char *indent;
    bson_iterator_from_buffer( &i, data );

    //ereport(INFO, (errmsg_internal("Entered my_bson_print for data= %s  i= %s  depth= %d", data, i, depth)));
    while ( bson_iterator_next( &i ) ) {
        bson_type t = bson_iterator_type( &i );
        if ( t == 0 )
            break;
        key = bson_iterator_key( &i );

        switch (depth) {
        case 0:
        	indent = "  ";
        	break;
        case 1:
        	indent = "    ";
        	break;
        case 2:
        	indent = "      ";
        	break;
        case 3:
        	indent = "        ";
        	break;
        default:
        	indent = "          ";
        }

        switch ( t ) {
        case BSON_DOUBLE:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %f",indent, key , t , bson_iterator_double( &i ) )));
            break;
        case BSON_STRING:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %s",indent, key , t , bson_iterator_string( &i ) )));
            break;
        case BSON_SYMBOL:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t SYMBOL: %s",indent, key , t , bson_iterator_string( &i ) )));
            break;
        case BSON_OID:
            bson_oid_to_string( bson_iterator_oid( &i ), oidhex );
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %s",indent, key , t , oidhex )));
            break;
        case BSON_BOOL:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %s",indent, key , t , bson_iterator_bool( &i ) ? "true" : "false" )));
            break;
        case BSON_DATE:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %ld",indent, key , t , ( long int )bson_iterator_date( &i ) )));
            break;
        case BSON_BINDATA:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t BSON_BINDATA",indent , key , t)));
            break;
        case BSON_UNDEFINED:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t BSON_UNDEFINED",indent, key , t )));
            break;
        case BSON_NULL:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t BSON_NULL",indent, key , t )));
            break;
        case BSON_REGEX:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t BSON_REGEX: %s",indent, key , t, bson_iterator_regex( &i ) )));
            break;
        case BSON_CODE:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t BSON_CODE: %s",indent, key , t, bson_iterator_code( &i ) )));
            break;
        case BSON_CODEWSCOPE:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t BSON_CODE_W_SCOPE: %s",indent, key , t, bson_iterator_code( &i ) )));
            bson_init( &scope );
            bson_iterator_code_scope( &i, &scope );
            ereport(INFO, (errmsg_internal( "\n\t SCOPE: " )));
            bson_print( &scope );
            break;
        case BSON_INT:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %d",indent, key , t , bson_iterator_int( &i ) )));
            break;
        case BSON_LONG:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t %lld",indent, key , t , ( uint64_t )bson_iterator_long( &i ) )));
            break;
        case BSON_TIMESTAMP:
            ts = bson_iterator_timestamp( &i );
            ereport(INFO, (errmsg_internal( "%s %s : %d \t i: %d, t: %d",indent, key , t, ts.i, ts.t )));
            break;
        case BSON_OBJECT:
        case BSON_ARRAY:
            ereport(INFO, (errmsg_internal( "%s %s : %d \t ",indent , key , t)));
            my_bson_print_raw( bson_iterator_value( &i ) , depth + 1 );
            break;
        default:
        	ereport(INFO, (errmsg_internal( "%s %s : %d \t can't print type : %d",indent , key , t , t )));
        }
    }
}
void my_bson_print( const bson *b ) {
    my_bson_print_raw( b->data , 0 );
}

/*
 * ApplicableOpExpressionList walks over all filter clauses that relate to this
 * foreign table, and chooses applicable clauses that we know we can translate
 * into Mongo queries. Currently, these clauses include comparison expressions
 * that have a column and a constant as arguments. For example, "o_orderdate >=
 * date '1994-01-01' + interval '1' year" is an applicable expression.
 */
List *
ApplicableOpExpressionList(RelOptInfo *baserel)
{
	List *opExpressionList = NIL;
	List *restrictInfoList = baserel->baserestrictinfo;
	ListCell *restrictInfoCell = NULL;

	foreach(restrictInfoCell, restrictInfoList)
	{
		RestrictInfo *restrictInfo = (RestrictInfo *) lfirst(restrictInfoCell);
		Expr *expression = restrictInfo->clause;
		NodeTag expressionType = 0;

		OpExpr *opExpression = NULL;
		char *operatorName = NULL;
		char *mongoOperatorName = NULL;
		List *argumentList = NIL;
		Var *column = NULL;
		Const *constant = NULL;
		bool equalsOperator = false;
		bool constantIsArray = false;

		/* we only support operator expressions */
		expressionType = nodeTag(expression);
		if (expressionType != T_OpExpr)
		{
			continue;
		}

		opExpression = (OpExpr *) expression;
		operatorName = get_opname(opExpression->opno);

		/* we only support =, <, >, <=, >=, and <> operators */
		if (strncmp(operatorName, EQUALITY_OPERATOR_NAME, NAMEDATALEN) == 0)
		{
			equalsOperator = true;
		}

		mongoOperatorName = MongoOperatorName(operatorName);
		if (!equalsOperator && mongoOperatorName == NULL)
		{
			ereport(INFO, (errmsg_internal("Ignoring unsupported operator %s", 
							               operatorName)));
			continue;
		}

		/*
		 * We only support simple binary operators that compare a column against
		 * a constant. If the expression is a tree, we don't recurse into it.
		 */
		argumentList = opExpression->args;
		column = (Var *) FindArgumentOfType(argumentList, T_Var);
		constant = (Const *) FindArgumentOfType(argumentList, T_Const);

		/*
		 * We don't push down operators where the constant is an array, since
		 * conditional operators for arrays in MongoDB aren't properly defined.
		 * For example, {similar_products : [ "B0009S4IJW", "6301964144" ]}
		 * finds results that are equal to the array, but {similar_products:
		 * {$gte: [ "B0009S4IJW", "6301964144" ]}} returns an empty set.
		 */
		if (constant != NULL)
		{
			Oid constantArrayTypeId = get_element_type(constant->consttype);
			if (constantArrayTypeId != InvalidOid)
			{
				constantIsArray = true;
				ereport(INFO, (errmsg_internal("Ignoring %s expression with array",
											   operatorName)));
			}
		}
		else
		{
			ereport(INFO, (errmsg_internal("Ignoring %s expression without a constant",
										   operatorName)));
		}

		if (column != NULL && constant != NULL && !constantIsArray)
		{
			opExpressionList = lappend(opExpressionList, opExpression);
		}
	}

	return opExpressionList;
}


/*
 * FindArgumentOfType walks over the given argument list, looks for an argument
 * with the given type, and returns the argument if it is found.
 */
static Expr *
FindArgumentOfType(List *argumentList, NodeTag argumentType)
{
	Expr *foundArgument = NULL;
	ListCell *argumentCell = NULL;

	foreach(argumentCell, argumentList)
	{
		Expr *argument = (Expr *) lfirst(argumentCell);
		if (nodeTag(argument) == argumentType)
		{
			foundArgument = argument;
			break;
		}
	}

	return foundArgument;
}


/*
 * QueryDocument takes in the applicable operator expressions for a relation and
 * converts these expressions into equivalent queries in MongoDB. For now, this
 * function can only transform simple comparison expressions, and returns these
 * transformed expressions in a BSON document. For example, simple expressions
 * "l_shipdate >= date '1994-01-01' AND l_shipdate < date '1995-01-01'" become
 * "l_shipdate: { $gte: new Date(757382400000), $lt: new Date(788918400000) }".
 */
bson *
QueryDocument(Oid relationId, List *opExpressionList, MongoFdwOptions* mongoFdwOptions,
		      struct HTAB *columnMappingHash)
{
	List *equalityOperatorList = NIL;
	List *comparisonOperatorList = NIL;
	List *columnList = NIL;
	ListCell *equalityOperatorCell = NULL;
	ListCell *columnCell = NULL;
	bson *queryDocument = NULL;
	int documentStatus = BSON_OK;
	char *prefix = "parent.";
	char *oidGeneratedKeySuffix = ".generated";
	int prefix_len = strlen(prefix);
	StringInfo columnNameInfo = NULL;

	ereport(DEBUG2, (errmsg_internal("Entered QueryDocument")));
	queryDocument = bson_create();
	bson_init(queryDocument);

	/*
	 * We distinguish between equality expressions and others since we need to
	 * insert the latter (<, >, <=, >=, <>) as separate sub-documents into the
	 * BSON query object.
	 */
	equalityOperatorList = EqualityOperatorList(opExpressionList);
	comparisonOperatorList = list_difference(opExpressionList, equalityOperatorList);

	/* append equality expressions to the query */
	foreach(equalityOperatorCell, equalityOperatorList)
	{
		OpExpr *equalityOperator = (OpExpr *) lfirst(equalityOperatorCell);
		Oid columnId = InvalidOid;
		char *columnName = NULL;
		int suffixLen = strlen(oidGeneratedKeySuffix);
		int columnNameLen = 0;
		char *dot = NULL;
		bson_type toBsonType = -1;
		bool handleFound = false;
		ColumnMapping *columnMapping = NULL;

		List *argumentList = equalityOperator->args;
		Var *column = (Var *) FindArgumentOfType(argumentList, T_Var);
		Const *constant = (Const *) FindArgumentOfType(argumentList, T_Const);

		void *hashKey;

		columnId = column->varattno;
		columnName = get_relid_attribute_name(relationId, columnId);
		hashKey = (void *) columnName;
		columnMapping = (ColumnMapping *) hash_search(columnMappingHash,
													  hashKey, HASH_FIND,
													  &handleFound);
		if (mongoFdwOptions->fieldName && *mongoFdwOptions->fieldName != '\0') {
			if (strncmp(columnName, prefix, prefix_len) == 0)
			{
				columnName = columnName + prefix_len; 
			}
			else
			{
				columnNameInfo = makeStringInfo();
				appendStringInfo(columnNameInfo, "%s.%s", mongoFdwOptions->fieldName,
								 columnName);
				columnName = columnNameInfo->data;
			}
		}

		columnNameLen = strlen(columnName);
		if (columnNameLen > suffixLen &&
			strcmp(columnName + (columnNameLen - suffixLen), oidGeneratedKeySuffix) == 0)
		{
			dot = columnName + (columnNameLen - suffixLen);
			/* Chop .generated off of the keyname to get the oid name */
			*dot = '\0';
			toBsonType = BSON_OID;
		}
		else if(columnMapping)
		{
			toBsonType = columnMapping->columnBsonType;
		}

		AppendConstantValue(queryDocument, columnName, toBsonType, constant);
		//my_bson_print(queryDocument, 0);

		if (dot) {
			*dot = '.';
		}
	}

	/*
	 * For comparison expressions, we need to group them by their columns and
	 * append all expressions that correspond to a column as one sub-document.
	 * Otherwise, even when we have two expressions to define the upper- and
	 * lower-bound of a range, Mongo uses only one of these expressions during
	 * an index search.
	 */
	columnList = UniqueColumnList(comparisonOperatorList);

	/* append comparison expressions, grouped by columns, to the query */
	foreach(columnCell, columnList)
	{
		Var *column = (Var *) lfirst(columnCell);
		Oid columnId = InvalidOid;
		char *columnName = NULL;
		List *columnOperatorList = NIL;
		ListCell *columnOperatorCell = NULL;
		int suffixLen = strlen(oidGeneratedKeySuffix);
		int columnNameLen = 0;
		char *dot = NULL;
		bson_type toBsonType = -1;
		ColumnMapping *columnMapping = NULL;
		bool handleFound = false;
		void *hashKey;

		columnId = column->varattno;
		columnName = get_relid_attribute_name(relationId, columnId);
		hashKey = (void *) columnName;
		columnMapping = (ColumnMapping *) hash_search(columnMappingHash,
													  hashKey, HASH_FIND,
													  &handleFound);
		if (mongoFdwOptions->fieldName && *mongoFdwOptions->fieldName != '\0') {
			if (strncmp(columnName, prefix, prefix_len) == 0)
			{
				columnName = columnName + prefix_len; 
			}
			else
			{
				columnNameInfo = makeStringInfo();
				appendStringInfo(columnNameInfo, "%s.%s", mongoFdwOptions->fieldName,
								 columnName);
				columnName = columnNameInfo->data;
			}
		}

		columnNameLen = strlen(columnName);
		if (columnNameLen > suffixLen &&
			strcmp(columnName + (columnNameLen - suffixLen), oidGeneratedKeySuffix) == 0)
		{
			dot = columnName + (columnNameLen - suffixLen);
			/* Chop .generated off of the keyname to get the oid name */
			*dot = '\0';
			toBsonType = BSON_OID;
		}
		else if(columnMapping)
		{
			toBsonType = columnMapping->columnBsonType;
		}

		/* find all expressions that correspond to the column */
		columnOperatorList = ColumnOperatorList(column, comparisonOperatorList);

		/* for comparison expressions, start a sub-document */
		bson_append_start_object(queryDocument, columnName);
		//my_bson_print(queryDocument, 0);

		if (dot) {
			*dot = '.';
		}

		foreach(columnOperatorCell, columnOperatorList)
		{
			OpExpr *columnOperator = (OpExpr *) lfirst(columnOperatorCell);
			char *operatorName = NULL;
			char *mongoOperatorName = NULL;

			List *argumentList = columnOperator->args;
			Const *constant = (Const *) FindArgumentOfType(argumentList, T_Const);

			operatorName = get_opname(columnOperator->opno);
			mongoOperatorName = MongoOperatorName(operatorName);

			AppendConstantValue(queryDocument, mongoOperatorName, toBsonType, constant);
			//my_bson_print(queryDocument, 0);
		}

		bson_append_finish_object(queryDocument);
		//my_bson_print(queryDocument, 0);
	}

	documentStatus = bson_finish(queryDocument);
	ereport(DEBUG2, (errmsg_internal("Leaving QueryDocument")));
	my_bson_print(queryDocument);
	if (documentStatus != BSON_OK)
	{
		ereport(ERROR, (errmsg("could not create document for query"),
						errhint("BSON error: %s", queryDocument->errstr)));
	}

	return queryDocument;
}


//bson *
//CommandQueryDocument(Oid relationId, List *opExpressionList, MongoFdwOptions* mongoFdwOptions,
//		      struct HTAB *columnMappingHash)
//{
//	List *equalityOperatorList = NIL;
//	List *comparisonOperatorList = NIL;
//	List *columnList = NIL;
//	ListCell *equalityOperatorCell = NULL;
//	ListCell *columnCell = NULL;
//	bson *queryDocument = NULL;
//	int documentStatus = BSON_OK;
//	char *prefix = "parent.";
//	char *oidGeneratedKeySuffix = ".generated";
//	int prefix_len = strlen(prefix);
//	StringInfo columnNameInfo = NULL;
//
//	ereport(INFO, (errmsg_internal("Entered CommandQueryDocument")));
//	ereport(INFO, (errmsg("collection= %s  unwindField= %s", mongoFdwOptions->collectionName,
//			mongoFdwOptions->unwindFieldName)));
//	char **tokens;
//	tokens = StrSplit(mongoFdwOptions->unwindFieldName, '.');
//	ereport(INFO, (errmsg("%s", *tokens)));
//	queryDocument = bson_create();
//	bson_init(queryDocument);
//	//bson_append_string(queryDocument, "aggregate", "users");
//	bson_append_string(queryDocument, "aggregate", mongoFdwOptions->collectionName);
//	bson_append_start_array(queryDocument, "pipeline");
//	if (tokens) {
//		int i;
//		char fieldPath[512];
//		strcpy(fieldPath, "$");
//		// we need to construct a string like "$field1" and "$field1.field2" etc.
//		ereport(INFO, (errmsg("fieldPath= %s", fieldPath)));
//		for (i=0; *(tokens+i); i++) {
//			if (i > 0) {
//				strcat(fieldPath, ".");
//			}
//			ereport(INFO, (errmsg("%d fieldPath= %s", i, fieldPath)));
//			strcat(fieldPath, *(tokens+i));
//			ereport(INFO, (errmsg("fieldPath= %s", fieldPath)));
//			char str[10];
//			sprintf(str, "%d", i);
//
//			bson_append_start_object(queryDocument, str);
//			bson_append_string(queryDocument, "$unwind", fieldPath);
//		    bson_append_finish_object(queryDocument);
//		    free(*(tokens+i));
//
////			bson_append_start_object(queryDocument, "0");
////			bson_append_string(queryDocument, "$unwind", "$likes");
////		    bson_append_finish_object(queryDocument);
//		}
//		free(tokens);
////		bson_append_start_object(queryDocument, "1");
////		bson_append_string(queryDocument, "$unwind", "$likes.plays");
////	    bson_append_finish_object(queryDocument);
//	}
//	bson_append_finish_array(queryDocument);
//	bson_finish(queryDocument);
//	ereport(INFO, (errmsg("queryDocument----------------->")));
//	my_bson_print(queryDocument);
//	return queryDocument;
//
//
//	/*
//	 * We distinguish between equality expressions and others since we need to
//	 * insert the latter (<, >, <=, >=, <>) as separate sub-documents into the
//	 * BSON query object.
//	 */
//	equalityOperatorList = EqualityOperatorList(opExpressionList);
//	comparisonOperatorList = list_difference(opExpressionList, equalityOperatorList);
//
//	/* append equality expressions to the query */
//	foreach(equalityOperatorCell, equalityOperatorList)
//	{
//		OpExpr *equalityOperator = (OpExpr *) lfirst(equalityOperatorCell);
//		Oid columnId = InvalidOid;
//		char *columnName = NULL;
//		int suffixLen = strlen(oidGeneratedKeySuffix);
//		int columnNameLen = 0;
//		char *dot = NULL;
//		bson_type toBsonType = -1;
//		bool handleFound = false;
//		ColumnMapping *columnMapping = NULL;
//		void *hashKey;
//
//		List *argumentList = equalityOperator->args;
//		Var *column = (Var *) FindArgumentOfType(argumentList, T_Var);
//		Const *constant = (Const *) FindArgumentOfType(argumentList, T_Const);
//
//		columnId = column->varattno;
//		columnName = get_relid_attribute_name(relationId, columnId);
//		hashKey = (void *) columnName;
//		columnMapping = (ColumnMapping *) hash_search(columnMappingHash,
//													  hashKey, HASH_FIND,
//													  &handleFound);
//		if (mongoFdwOptions->fieldName && *mongoFdwOptions->fieldName != '\0') {
//			if (strncmp(columnName, prefix, prefix_len) == 0)
//			{
//				columnName = columnName + prefix_len;
//			}
//			else
//			{
//				columnNameInfo = makeStringInfo();
//				appendStringInfo(columnNameInfo, "%s.%s", mongoFdwOptions->fieldName,
//								 columnName);
//				columnName = columnNameInfo->data;
//			}
//		}
//
//		columnNameLen = strlen(columnName);
//		if (columnNameLen > suffixLen &&
//			strcmp(columnName + (columnNameLen - suffixLen), oidGeneratedKeySuffix) == 0)
//		{
//			dot = columnName + (columnNameLen - suffixLen);
//			/* Chop .generated off of the keyname to get the oid name */
//			*dot = '\0';
//			toBsonType = BSON_OID;
//		}
//		else if(columnMapping)
//		{
//			toBsonType = columnMapping->columnBsonType;
//		}
//
//		AppendConstantValue(queryDocument, columnName, toBsonType, constant);
//		//my_bson_print(queryDocument, 0);
//
//		if (dot) {
//			*dot = '.';
//		}
//	}
//
//	/*
//	 * For comparison expressions, we need to group them by their columns and
//	 * append all expressions that correspond to a column as one sub-document.
//	 * Otherwise, even when we have two expressions to define the upper- and
//	 * lower-bound of a range, Mongo uses only one of these expressions during
//	 * an index search.
//	 */
//	columnList = UniqueColumnList(comparisonOperatorList);
//
//	/* append comparison expressions, grouped by columns, to the query */
//	foreach(columnCell, columnList)
//	{
//		Var *column = (Var *) lfirst(columnCell);
//		Oid columnId = InvalidOid;
//		char *columnName = NULL;
//		List *columnOperatorList = NIL;
//		ListCell *columnOperatorCell = NULL;
//		int suffixLen = strlen(oidGeneratedKeySuffix);
//		int columnNameLen = 0;
//		char *dot = NULL;
//		bson_type toBsonType = -1;
//		ColumnMapping *columnMapping = NULL;
//		bool handleFound = false;
//		void *hashKey;
//
//		columnId = column->varattno;
//		columnName = get_relid_attribute_name(relationId, columnId);
//		hashKey = (void *) columnName;
//		columnMapping = (ColumnMapping *) hash_search(columnMappingHash,
//													  hashKey, HASH_FIND,
//													  &handleFound);
//		if (mongoFdwOptions->fieldName && *mongoFdwOptions->fieldName != '\0') {
//			if (strncmp(columnName, prefix, prefix_len) == 0)
//			{
//				columnName = columnName + prefix_len;
//			}
//			else
//			{
//				columnNameInfo = makeStringInfo();
//				appendStringInfo(columnNameInfo, "%s.%s", mongoFdwOptions->fieldName,
//								 columnName);
//				columnName = columnNameInfo->data;
//			}
//		}
//
//		columnNameLen = strlen(columnName);
//		if (columnNameLen > suffixLen &&
//			strcmp(columnName + (columnNameLen - suffixLen), oidGeneratedKeySuffix) == 0)
//		{
//			dot = columnName + (columnNameLen - suffixLen);
//			/* Chop .generated off of the keyname to get the oid name */
//			*dot = '\0';
//			toBsonType = BSON_OID;
//		}
//		else if(columnMapping)
//		{
//			toBsonType = columnMapping->columnBsonType;
//		}
//
//		/* find all expressions that correspond to the column */
//		columnOperatorList = ColumnOperatorList(column, comparisonOperatorList);
//
//		/* for comparison expressions, start a sub-document */
//		bson_append_start_object(queryDocument, columnName);
//		//my_bson_print(queryDocument, 0);
//
//		if (dot) {
//			*dot = '.';
//		}
//
//		foreach(columnOperatorCell, columnOperatorList)
//		{
//			OpExpr *columnOperator = (OpExpr *) lfirst(columnOperatorCell);
//			char *operatorName = NULL;
//			char *mongoOperatorName = NULL;
//
//			List *argumentList = columnOperator->args;
//			Const *constant = (Const *) FindArgumentOfType(argumentList, T_Const);
//
//			operatorName = get_opname(columnOperator->opno);
//			mongoOperatorName = MongoOperatorName(operatorName);
//
//			AppendConstantValue(queryDocument, mongoOperatorName, toBsonType, constant);
//			//my_bson_print(queryDocument, 0);
//		}
//
//		bson_append_finish_object(queryDocument);
//		//my_bson_print(queryDocument, 0);
//	}
//
//	documentStatus = bson_finish(queryDocument);
//	ereport(INFO, (errmsg_internal("Leaving QueryDocument")));
//	my_bson_print(queryDocument);
//	if (documentStatus != BSON_OK)
//	{
//		ereport(ERROR, (errmsg("could not create document for query"),
//						errhint("BSON error: %s", queryDocument->errstr)));
//	}
//
//	return queryDocument;
//}
/*
 * MongoOperatorName takes in the given PostgreSQL comparison operator name, and
 * returns its equivalent in MongoDB.
 */
static char *
MongoOperatorName(const char *operatorName)
{
	const char *mongoOperatorName = NULL;
	const int32 nameCount = 5;
	static const char *nameMappings[][2] = { { "<", "$lt" },
											 { ">", "$gt" },
											 { "<=", "$lte" },
											 { ">=", "$gte" },
											 { "<>", "$ne" } };

	int32 nameIndex = 0;
	for (nameIndex = 0; nameIndex < nameCount; nameIndex++)
	{
		const char *pgOperatorName = nameMappings[nameIndex][0];
		if (strncmp(pgOperatorName, operatorName, NAMEDATALEN) == 0)
		{
			mongoOperatorName = nameMappings[nameIndex][1];
			break;
		}
	}

	return (char *) mongoOperatorName;
}


/*
 * EqualityOperatorList finds the equality (=) operators in the given list, and
 * returns these operators in a new list.
 */
static List *
EqualityOperatorList(List *operatorList)
{
	List *equalityOperatorList = NIL;
	ListCell *operatorCell = NULL;

	foreach(operatorCell, operatorList)
	{
		OpExpr *operator = (OpExpr *) lfirst(operatorCell);
		char *operatorName = NULL;

		operatorName = get_opname(operator->opno);
		if (strncmp(operatorName, EQUALITY_OPERATOR_NAME, NAMEDATALEN) == 0)
		{
			equalityOperatorList = lappend(equalityOperatorList, operator);
		}
	}

	return equalityOperatorList;
}


/*
 * UniqueColumnList walks over the given operator list, and extracts the column
 * argument in each operator. The function then de-duplicates extracted columns,
 * and returns them in a new list.
 */
static List *
UniqueColumnList(List *operatorList)
{
	List *uniqueColumnList = NIL;
	ListCell *operatorCell = NULL;

	foreach(operatorCell, operatorList)
	{
		OpExpr *operator = (OpExpr *) lfirst(operatorCell);
		List *argumentList = operator->args;
		Var *column = (Var *) FindArgumentOfType(argumentList, T_Var);

		/* list membership is determined via column's equal() function */
		uniqueColumnList = list_append_unique(uniqueColumnList, column);
	}

	return uniqueColumnList;
}


/*
 * ColumnOperatorList finds all expressions that correspond to the given column,
 * and returns them in a new list.
 */
static List *
ColumnOperatorList(Var *column, List *operatorList)
{
	List *columnOperatorList = NIL;
	ListCell *operatorCell = NULL;

	foreach(operatorCell, operatorList)
	{
		OpExpr *operator = (OpExpr *) lfirst(operatorCell);
		List *argumentList = operator->args;

		Var *foundColumn = (Var *) FindArgumentOfType(argumentList, T_Var);
		if (equal(column, foundColumn))
		{
			columnOperatorList = lappend(columnOperatorList, operator);
		}
	}

	return columnOperatorList;
}

static bool
AppendBsonInt(bson *queryDocument, const char *keyName,
			  const bson_type toBsonType, int value)
{
	bool appended = false;
	switch(toBsonType)
	{
		case BSON_STRING:
		{
			char *result = palloc0(22 * sizeof(char));
			snprintf(result, 22, "%d", value);
			bson_append_string(queryDocument, keyName, result);
			appended = true;
			break;
		}
		case BSON_DATE:
		{
			bson_append_date(queryDocument, keyName, value);
			appended = true;
			break;
		}
		case BSON_INT:
		case BSON_LONG:
		case BSON_DOUBLE:
		default:
		{
			bson_append_int(queryDocument, keyName, value);
			appended = true;
			break;
		}
	}
	return appended;
}

static bool
AppendBsonLong(bson *queryDocument, const char *keyName,
			  const bson_type toBsonType, long value)
{
	bool appended = false;
	switch(toBsonType)
	{
		case BSON_STRING:
		{
			char *result = palloc0(22 * sizeof(char));
			snprintf(result, 22, "%ld", value);
			bson_append_string(queryDocument, keyName, result);
			appended = true;
			break;
		}
		case BSON_DATE:
		{
			bson_append_date(queryDocument, keyName, value);
			appended = true;
			break;
		}
		case BSON_INT:
		case BSON_LONG:
		case BSON_DOUBLE:
		default:
		{
			bson_append_long(queryDocument, keyName, value);
			appended = true;
			break;
		}
	}
	return appended;
}

static bool
AppendBsonDouble(bson *queryDocument, const char *keyName,
			  const bson_type toBsonType, double value)
{
	bool appended = false;
	switch(toBsonType)
	{
		case BSON_STRING:
		{
			char *result = palloc0(22 * sizeof(char));
			snprintf(result, 22, "%g", value);
			bson_append_string(queryDocument, keyName, result);
			appended = true;
			break;
		}
		case BSON_DATE:
		{
			bson_append_date(queryDocument, keyName, (long) value);
			appended = true;
			break;
		}
		case BSON_INT:
		case BSON_LONG:
		case BSON_DOUBLE:
		default:
		{
			bson_append_double(queryDocument, keyName, value);
			appended = true;
			break;
		}
	}
	return appended;
}

static bool
AppendBsonString(bson *queryDocument, const char *keyName,
			     const bson_type toBsonType, char *value)
{
	bool appended = false;
	switch(toBsonType)
	{
		case BSON_INT:
		case BSON_LONG:
		{
			long parsed = 0;
			if(ParseLong(value, &parsed))
			{
				bson_append_long(queryDocument, keyName, parsed);
				appended = true;
			}
			break;
		}
		case BSON_DOUBLE:
		{
			double parsed = 0.0;
			if(ParseDouble(value, &parsed))
			{
				bson_append_double(queryDocument, keyName, parsed);
				appended = true;
			}
			break;
		}
		case BSON_OID:
		{
			bson_oid_t bsonObjectId;
			memset(bsonObjectId.bytes, 0, sizeof(bsonObjectId.bytes));
			bson_oid_from_string(&bsonObjectId, value);
			bson_append_oid(queryDocument, keyName, &bsonObjectId);
			appended = true;
			break;
		}
		case BSON_BOOL:
		case BSON_STRING:
		default:
		{
			bson_append_string(queryDocument, keyName, value);
			appended = true;
			break;
		}
	}
	return appended;
}

static bool
AppendBsonDate(bson *queryDocument, const char *keyName,
			   const bson_type toBsonType, long valueMilliSecs)
{
	bool appended = false;
	switch(toBsonType)
	{
		case BSON_INT:
		case BSON_LONG:
		case BSON_DOUBLE:
		{
			long valueSecs = valueMilliSecs / 1000;
			ereport(INFO, (errmsg("Appending date as long %s: %ld", keyName, valueSecs)));
			bson_append_long(queryDocument, keyName, valueSecs);
			appended = true;
			break;
		}
		case BSON_OID:
		{
			/* Generate an oid with a generated time at the time we're querying */
			bson_oid_t oid;
			time_t t = valueMilliSecs / 1000;
			bson_big_endian32(&oid.ints[0], &t);
			oid.ints[1] = 0;
			oid.ints[2] = 0;
			bson_append_oid(queryDocument, keyName, &oid);
			appended = true;
			break;
		}
		case BSON_DATE:
		default:
		{
			ereport(INFO, (errmsg("Appending date as date %s: %ld", keyName, valueMilliSecs)));
			bson_append_date(queryDocument, keyName, valueMilliSecs);
			appended = true;
			break;
		}
	}
	return appended;
}

/*
 * AppendConstantValue appends to the query document the key name and constant
 * value. The function translates the constant value from its PostgreSQL type to
 * its MongoDB equivalent.
 */
static void
AppendConstantValue(bson *queryDocument, const char *keyName,
					const bson_type toBsonType, Const *constant)
{
	Datum constantValue = constant->constvalue;
	Oid constantTypeId = constant->consttype;

	bool constantNull = constant->constisnull;
	if (constantNull)
	{
		bson_append_null(queryDocument, keyName);
		return;
	}

	switch(constantTypeId)
	{
		case INT2OID:
		{
			int16 value = DatumGetInt16(constantValue);
			AppendBsonInt(queryDocument, keyName, toBsonType, (int) value);
			break;
		}
		case INT4OID:
		{
			int32 value = DatumGetInt32(constantValue);
			AppendBsonInt(queryDocument, keyName, toBsonType, value);
			break;
		}
		case INT8OID:
		{
			int64 value = DatumGetInt64(constantValue);
			AppendBsonLong(queryDocument, keyName, toBsonType, value);
			break;
		}
		case FLOAT4OID:
		{
			float4 value = DatumGetFloat4(constantValue);
			AppendBsonDouble(queryDocument, keyName, toBsonType, (double) value);
			break;
		}
		case FLOAT8OID:
		{
			float8 value = DatumGetFloat8(constantValue);
			AppendBsonDouble(queryDocument, keyName, toBsonType, value);
			break;
		}
		case NUMERICOID:
		{
			Datum valueDatum = DirectFunctionCall1(numeric_float8, constantValue);
			float8 value = DatumGetFloat8(valueDatum);
			AppendBsonDouble(queryDocument, keyName, toBsonType, value);
			break;
		}
		case BOOLOID:
		{
			bool value = DatumGetBool(constantValue);
			bson_append_int(queryDocument, keyName, (int) value);
			break;
		}
		case BPCHAROID:
		case VARCHAROID:
		case TEXTOID:
		{
			char *outputString = NULL;
			Oid outputFunctionId = InvalidOid;
			bool typeVarLength = false;

			getTypeOutputInfo(constantTypeId, &outputFunctionId, &typeVarLength);
			outputString = OidOutputFunctionCall(outputFunctionId, constantValue);

			AppendBsonString(queryDocument, keyName, toBsonType, outputString);
			break;
		}
	    case NAMEOID:
		{
			char *outputString = NULL;
			Oid outputFunctionId = InvalidOid;
			bool typeVarLength = false;
			bson_oid_t bsonObjectId;
			memset(bsonObjectId.bytes, 0, sizeof(bsonObjectId.bytes));

			getTypeOutputInfo(constantTypeId, &outputFunctionId, &typeVarLength);
			outputString = OidOutputFunctionCall(outputFunctionId, constantValue);
			bson_oid_from_string(&bsonObjectId, outputString);

			bson_append_oid(queryDocument, keyName, &bsonObjectId);
			break;
		}
		case DATEOID:
		{
			Datum valueDatum = DirectFunctionCall1(date_timestamp, constantValue);
			Timestamp valueTimestamp = DatumGetTimestamp(valueDatum);
			int64 valueMicroSecs = valueTimestamp + POSTGRES_TO_UNIX_EPOCH_USECS;
			int64 valueMilliSecs = valueMicroSecs / 1000;
			AppendBsonDate(queryDocument, keyName, toBsonType, valueMilliSecs);
			break;
		}
		case TIMESTAMPOID:
		case TIMESTAMPTZOID:
		{
			Timestamp valueTimestamp = DatumGetTimestamp(constantValue);
			int64 valueMicroSecs = valueTimestamp + POSTGRES_TO_UNIX_EPOCH_USECS;
			int64 valueMilliSecs = valueMicroSecs / 1000;
			AppendBsonDate(queryDocument, keyName, toBsonType, valueMilliSecs);
			break;
		}
		default:
		{
			/*
			 * We currently error out on other data types. Some types such as
			 * byte arrays are easy to add, but they need testing. Other types
			 * such as money or inet, do not have equivalents in MongoDB.
			 */
			ereport(ERROR, (errcode(ERRCODE_FDW_INVALID_DATA_TYPE),
							errmsg("cannot convert constant value to BSON value"),
							errhint("Constant value data type: %u", constantTypeId)));
			break;
		}
	}
}


/*
 * ColumnList takes in the planner's information about this foreign table. The
 * function then finds all columns needed for query execution, including those
 * used in projections, joins, and filter clauses, de-duplicates these columns,
 * and returns them in a new list.
 */
List *
ColumnList(RelOptInfo *baserel)
{
	List *columnList = NIL;
	List *neededColumnList = NIL;
	AttrNumber columnIndex = 1;
	AttrNumber columnCount = baserel->max_attr;
	List *targetColumnList = baserel->reltargetlist;
	List *restrictInfoList = baserel->baserestrictinfo;
	ListCell *restrictInfoCell = NULL;

	/* first add the columns used in joins and projections */
	neededColumnList = list_copy(targetColumnList);

	/* then walk over all restriction clauses, and pull up any used columns */
	foreach(restrictInfoCell, restrictInfoList)
	{
		RestrictInfo *restrictInfo = (RestrictInfo *) lfirst(restrictInfoCell);
		Node *restrictClause = (Node *) restrictInfo->clause;
		List *clauseColumnList = NIL;

		/* recursively pull up any columns used in the restriction clause */
		clauseColumnList = pull_var_clause(restrictClause,
										   PVC_RECURSE_AGGREGATES,
										   PVC_RECURSE_PLACEHOLDERS);

		neededColumnList = list_union(neededColumnList, clauseColumnList);
	}

	/* walk over all column definitions, and de-duplicate column list */
	for (columnIndex = 1; columnIndex <= columnCount; columnIndex++)
	{
		ListCell *neededColumnCell = NULL;
		Var *column = NULL;

		/* look for this column in the needed column list */
		foreach(neededColumnCell, neededColumnList)
		{
			Var *neededColumn = (Var *) lfirst(neededColumnCell);
			if (neededColumn->varattno == columnIndex)
			{
				column = neededColumn;
				break;
			}
		}

		if (column != NULL)
		{
			columnList = lappend(columnList, column);
		}
	}

	return columnList;
}

char** StrSplit(char* a_str, const char a_delim)
{
    char** result    = 0;
    size_t count     = 0;
    char* tmp        = a_str;
    char* last_comma = 0;

    /* Count how many elements will be extracted. */
    while (*tmp)
    {
        if (a_delim == *tmp)
        {
            count++;
            last_comma = tmp;
        }
        tmp++;
    }

    /* Add space for trailing token. */
    count += last_comma < (a_str + strlen(a_str) - 1);

    /* Add space for terminating null string so caller
       knows where the list of returned strings ends. */
    count++;

    result = malloc(sizeof(char*) * count);

    if (result)
    {
        size_t idx  = 0;
        //char* token = strtok(a_str, ",");
        char* token = strtok(a_str, &a_delim);

        while (token)
        {
            assert(idx < count);
            *(result + idx++) = strdup(token);
            //token = strtok(0, ",");
            token = strtok(0, &a_delim);
        }
        assert(idx == count - 1);
        *(result + idx) = 0;
    }

    return result;
}
