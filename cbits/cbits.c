#include "cbits.h"

void setStrArrayItem(StrPtr *array, uint64_t pos, const char *value)
{
	array[pos] = value;
}
