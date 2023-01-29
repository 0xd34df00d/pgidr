#pragma once

#include <stdint.h>

typedef const char *StrPtr;

void setStrArrayItem(StrPtr *array, uint64_t pos, const char *value);
