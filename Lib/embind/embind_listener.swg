#include <emscripten/threading.h>
#include <emscripten/proxying.h>

typedef union em_variant_val { int i; int64_t i64; float f; double d; void *vp; char *cp; } em_variant_val;
#define EM_QUEUED_CALL_MAX_ARGS 11
typedef struct em_queued_call { int functionEnum; void *functionPtr; _Atomic uint32_t operationDone; em_variant_val args[EM_QUEUED_JS_CALL_MAX_ARGS]; em_variant_val returnValue; void *satelliteData; int calleeDelete; } em_queued_call;
