plugins {
    application
    java
    id("checkstyle")
    id("pmd")
    id("com.github.spotbugs") version "5.0.14"
}

repositories {
    mavenCentral()
}

dependencies {
    implementation("com.google.guava:guava:31.0.1-jre")
    testImplementation("org.junit.jupiter:junit-jupiter-api:5.8.2")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:5.8.2")
}

tasks.test {
    useJUnitPlatform()
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(17))
    }
}

application {
    mainClass.set("org.example.Pentago")
}

pmd {
    toolVersion = "6.55.0"
    ruleSets = listOf("category/java/bestpractices.xml", "category/java/errorprone.xml")
    isConsoleOutput = true
}

spotbugs {
    toolVersion = "4.8.0"
}

// === Checkstyle ===
checkstyle {
    toolVersion = "10.2"
    val configFile = file("config/checkstyle/checkstyle.xml")
    if (!configFile.exists()) {
        throw GradleException("Checkstyle config not found: $configFile")
    }
    config = resources.text.fromFile(configFile)
    isShowViolations = true
}

// Fix classpath for checkstyleMain and checkstyleTest tasks
tasks.named<Checkstyle>("checkstyleMain") {
    classpath = sourceSets["main"].runtimeClasspath // Ensure proper runtime classpath for main
}

tasks.named<Checkstyle>("checkstyleTest") {
    classpath = sourceSets["test"].runtimeClasspath // Ensure proper runtime classpath for test
}

// === Safe Exec Task ===
tasks.register("bEx") {
    group = "build"
    description = "Runs build and test ignoring static analysis failures"
    dependsOn("build", "test")
    outputs.upToDateWhen { false } // Force task to always run
}

// Global enforce failure settings for PMD, Checkstyle, and SpotBugs tasks
tasks.withType<org.gradle.api.plugins.quality.Pmd>().configureEach {
    ignoreFailures = false  // Fail build if PMD violations are found
}

tasks.withType<Checkstyle>().configureEach {
    ignoreFailures = false  // Fail build if Checkstyle violations are found
}

tasks.withType<com.github.spotbugs.snom.SpotBugsTask>().configureEach {
    ignoreFailures = false  // Fail build if SpotBugs violations are found
}
